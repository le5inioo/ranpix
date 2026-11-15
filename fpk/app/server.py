#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""RanPix - fnOS native random image API.

Zero third-party dependencies: Python standard library only.
Every first-level subdirectory of the image root becomes one API endpoint.

Two access paths are served by the same process:
  * direct TCP   http://<nas-ip>:<port>/          (configurable port, LAN / API use)
  * fnOS gateway https://<nas-host>/app/ranpix/  (same-origin reverse proxy,
    used by the desktop icon and the mobile app; independent of the TCP port)

The gateway talks to a Unix socket in the app root; fnOS forwards requests
with the /app/ranpix prefix intact, so the handler strips it and injects the
same prefix into every link produced by the management page.
Port and image root are configurable via the install wizard, the app settings
page, or the built-in management page (stored in TRIM_PKGETC/config.json).
"""

import html
import ipaddress
import json
import os
import random
import re
import shutil
import socket
import socketserver
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from string import Template
from urllib.parse import parse_qs, quote, unquote, urlparse

APPNAME = "ranpix"
APP_TITLE = "RanPix"
VERSION = "1.1.1"
DEFAULT_PORT = 18580
GATEWAY_PREFIX = "/app/ranpix"
SOCKET_NAME = "ranpix.sock"
SUPPORTED = (".jpg", ".jpeg", ".png", ".webp", ".gif", ".bmp", ".tiff")
MIME = {
    ".jpg": "image/jpeg", ".jpeg": "image/jpeg", ".png": "image/png",
    ".webp": "image/webp", ".gif": "image/gif", ".bmp": "image/bmp",
    ".tiff": "image/tiff",
}
SAFE_NAME = re.compile(r"^[^/\\]{1,128}$")
FORBIDDEN_ROOTS = ("/", "/bin", "/boot", "/dev", "/etc", "/lib", "/lib64",
                   "/proc", "/root", "/sbin", "/sys", "/usr")
VAR_DIR = os.environ.get("TRIM_PKGVAR") or os.path.join(os.path.dirname(os.path.abspath(__file__)), "var")
ETC_DIR = os.environ.get("TRIM_PKGETC") or os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.path.join(ETC_DIR, "config.json")
LOG_PATH = os.path.join(VAR_DIR, "server.log")
SOCKET_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), SOCKET_NAME)
BOUND_PORT = DEFAULT_PORT
GATEWAY_READY = False

try:
    os.makedirs(VAR_DIR, exist_ok=True)
except OSError:
    pass


def log(msg):
    line = "%s %s" % (time.strftime("%Y-%m-%d %H:%M:%S"), msg)
    try:
        with open(LOG_PATH, "a", encoding="utf-8") as fh:
            fh.write(line + "\n")
    except OSError:
        pass
    print(line, flush=True)


def valid_port(value):
    try:
        p = int(value)
    except (TypeError, ValueError):
        return 0
    return p if 1024 <= p <= 65535 else 0


def valid_ttl(value):
    try:
        n = int(value)
    except (TypeError, ValueError):
        return 0
    return n if 1 <= n <= 3600 else 0


def valid_root(value):
    """Return (normalised_path, error). Empty value means the default share."""
    raw = (value or "").strip()
    if not raw:
        return "", ""
    path = os.path.normpath(raw)
    if not os.path.isabs(path):
        return "", "图片根目录必须是绝对路径"
    if path in FORBIDDEN_ROOTS or path.startswith("/etc/") or path.startswith("/proc/"):
        return "", "出于安全考虑，不允许把系统目录作为图片根目录"
    if not os.path.isdir(path):
        return "", "目录不存在：%s" % path
    try:
        with os.scandir(path) as it:
            next(it, None)
    except OSError as exc:
        return "", ("目录不可读：%s。顶层文件夹到「设置 → 应用管理 → RanPix → 权限设置」授权；"
                    "子文件夹到「文件管理 → 详细信息 → 权限 → 高级」启用继承父级权限"
                    % (exc.strerror or "权限不足"))
    return path, ""


def detect_share():
    """Locate the fnOS data-share created for this app."""
    for key in ("TRIM_DATA_ACCESSIBLE_PATHS", "TRIM_DATA_SHARE_PATHS"):
        for candidate in os.environ.get(key, "").split(":"):
            if candidate and os.path.isdir(candidate):
                return candidate
    base = os.path.join("/var/apps", APPNAME, "shares")
    preferred = os.path.join(base, APPNAME)
    if os.path.isdir(preferred):
        return preferred
    try:
        subs = sorted(os.path.join(base, n) for n in os.listdir(base)
                      if os.path.isdir(os.path.join(base, n)))
        if subs:
            return subs[0]
    except OSError:
        pass
    return preferred


def lan_ipv4():
    """Best-effort LAN IPv4 of this NAS. UDP connect sends no packet, it just
    asks the kernel which source address the default route would use."""
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("223.5.5.5", 80))
        ip = s.getsockname()[0]
        s.close()
        if ip and not ip.startswith("127."):
            return ip
    except OSError:
        pass
    return ""


def direct_base(cfg, host_header=""):
    """URL that opens in ANY browser without a fnOS login token.

    /app/<app>/ is guarded by fnOS unified authentication: a gateway URL
    copied out of the mobile app into a normal browser answers `invalid token`.
    The plain TCP port has no such requirement, so that is what we share.
    """
    host = (host_header or "").strip()
    if host.startswith("[") and "]" in host:
        host = host[1:host.find("]")]
    else:
        host = host.split(":")[0]
    try:
        addr = ipaddress.ip_address(host)
        ok = addr.version == 4 and not addr.is_loopback and not addr.is_unspecified
    except ValueError:
        ok = False
    if not ok:
        host = lan_ipv4() or host
    if not host:
        host = "127.0.0.1"
    return "http://%s:%d" % (host, cfg["port"])


def load_config():
    cfg = {"image_root": "", "port": DEFAULT_PORT, "cache_ttl": 30}
    try:
        with open(CONFIG_PATH, "r", encoding="utf-8") as fh:
            data = json.load(fh)
            if isinstance(data, dict):
                cfg.update({k: v for k, v in data.items() if k in cfg})
    except (OSError, ValueError):
        pass
    port = valid_port(cfg.get("port"))
    if not port:
        port = valid_port(os.environ.get("RANPIX_PORT") or
                          os.environ.get("PORT") or
                          os.environ.get("TRIM_SERVICE_PORT")) or DEFAULT_PORT
    cfg["port"] = port
    root = (cfg.get("image_root") or "").strip()
    if not root:
        root = (os.environ.get("RANPIX_IMAGE_ROOT") or
                os.environ.get("IMAGE_ROOT") or "").strip()
    cfg["image_root"] = os.path.normpath(root) if root else detect_share()
    cfg["cache_ttl"] = valid_ttl(cfg.get("cache_ttl")) or 30
    return cfg


def save_config(cfg):
    with open(CONFIG_PATH, "w", encoding="utf-8") as fh:
        json.dump({"image_root": cfg.get("image_root", ""),
                   "port": cfg["port"],
                   "cache_ttl": cfg["cache_ttl"]}, fh,
                  ensure_ascii=False, indent=2)
    try:
        os.chmod(CONFIG_PATH, 0o666)
    except OSError:
        pass


def schedule_execv():
    """Re-exec in place: config is re-read and the PID stays valid."""
    def _restart():
        time.sleep(0.7)
        os.execv(sys.executable, [sys.executable, os.path.abspath(__file__)])
    threading.Thread(target=_restart, daemon=True).start()


_scan_errors = {}


def scan_tree(folder):
    """Return (images, errors). os.walk silently drops unreadable dirs,
    so collect the OSError explicitly instead of reporting a misleading 0."""
    found, errors = [], []

    def onerror(exc):
        errors.append(exc)

    for base, dirs, names in os.walk(folder, onerror=onerror):
        dirs[:] = [d for d in dirs if not d.startswith(".")]
        for name in names:
            if name.lower().endswith(SUPPORTED):
                found.append(os.path.join(base, name))
    if not errors:
        try:
            os.listdir(folder)
        except OSError as exc:
            errors.append(exc)
    return found, errors


def discover(root):
    """Return {category_name: [image paths]}. '' holds images at root level."""
    result = {}
    errors = {}
    try:
        entries = sorted(os.listdir(root))
    except OSError as exc:
        _scan_errors.clear()
        _scan_errors[""] = exc.strerror or str(exc)
        return result
    loose = []
    for name in entries:
        path = os.path.join(root, name)
        if name.startswith("."):
            continue
        if os.path.isdir(path):
            found, errs = scan_tree(path)
            result[name] = found
            if errs:
                errors[name] = errs[0].strerror or str(errs[0])
        elif os.path.isfile(path) and name.lower().endswith(SUPPORTED):
            loose.append(path)
    if loose:
        result[""] = loose
    _scan_errors.clear()
    _scan_errors.update(errors)
    return result


_cache = {"ts": 0.0, "root": None, "cats": {}}


def categories():
    cfg = load_config()
    root = cfg["image_root"]
    if _cache["root"] != root or time.time() - _cache["ts"] > cfg["cache_ttl"]:
        _cache["cats"] = discover(root)
        _cache["root"] = root
        _cache["ts"] = time.time()
    return _cache["cats"]


def resolve_category(name, cats):
    """Map a requested API name to a real folder name, ignoring case.

    Exact match always wins. When several folders differ only by case we
    report the ambiguity instead of silently serving the wrong one.
    Returns (canonical_name_or_None, ambiguous_names).
    """
    if name in cats:
        return name, []
    folded = {}
    for real in cats:
        if real:
            folded.setdefault(real.casefold(), []).append(real)
    matches = folded.get(name.casefold(), [])
    if len(matches) == 1:
        return matches[0], []
    return None, matches


def root_status(cfg):
    root = cfg["image_root"]
    info = {"path": root, "exists": os.path.isdir(root), "readable": False,
            "hint": "使用默认应用共享目录"}
    if not info["exists"]:
        info["hint"] = "目录不存在，请检查路径或重新安装应用"
        return info
    try:
        with os.scandir(root) as it:
            next(it, None)
        info["readable"] = True
        info["hint"] = "可正常读取"
    except OSError as exc:
        info["hint"] = ("目录不可读（%s）→ 顶层文件夹在 设置 → 应用管理 → RanPix → 权限设置 授权；"
                        "子文件夹在 文件管理 → 详细信息 → 权限 → 高级 启用继承") % (
            exc.strerror or "权限不足")
    bad = [n for n in _scan_errors if n]
    if bad:
        info["hint"] += "；但 %d 个子目录无读取权限：%s（详见接口列表）" % (
            len(bad), "、".join("/" + n for n in sorted(bad)))
    return info


PAGE = Template("""<!doctype html><html lang="zh-CN"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<title>$title · 随机图片 API</title><style>
:root{color-scheme:light}*{box-sizing:border-box}
html,body{max-width:100%;overflow-x:hidden;overscroll-behavior-x:none}
body{margin:0;background:#f5f7fa;color:#1f2328;-webkit-text-size-adjust:100%;touch-action:pan-y;
font:14px/1.6 -apple-system,BlinkMacSystemFont,"Segoe UI","Microsoft YaHei",sans-serif}
.wrap{max-width:920px;margin:32px auto 60px;padding:0 20px}
.head{display:flex;flex-wrap:wrap;align-items:center;gap:8px 12px;margin-bottom:6px;min-width:0}
.head img{width:40px;height:40px;border-radius:10px;flex:none}
h1{font-size:21px;font-weight:600;margin:0;min-width:0;overflow-wrap:anywhere}
p.sub{color:#656d76;margin:0 0 22px;overflow-wrap:anywhere}
.card{background:#fff;border:1px solid #e3e6ea;border-radius:12px;padding:18px 20px;margin-bottom:16px;min-width:0}
.card h2{font-size:15px;font-weight:600;margin:0 0 14px}
code{background:#f1f3f5;padding:2px 6px;border-radius:5px;font-size:12.5px;
word-break:break-all;overflow-wrap:anywhere}
a{color:#185fa5;text-decoration:none;overflow-wrap:anywhere}
input[type=text],input[type=number]{border:1px solid #d5d9de;border-radius:6px;
padding:7px 10px;font:inherit;width:100%;min-width:0;background:#fff;color:#1f2328}
label{display:block;font-size:13px;color:#656d76;margin-bottom:5px}
.grid{display:flex;flex-wrap:wrap;gap:12px;align-items:flex-end}
.grid>div{min-width:0;flex:1 1 210px}
.grid>div.sm{flex:0 1 170px}
.grid>div.grow{flex:1 1 260px}
.stats{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1fr);gap:12px 20px}
.stat{min-width:0}
.stat .k{font-size:12.5px;color:#656d76}
.stat .v{margin-top:1px;min-width:0;overflow-wrap:anywhere}
.apis{border-top:1px solid #eef0f2}
.api{display:flex;flex-wrap:wrap;align-items:center;gap:6px 10px;
padding:10px 0;border-bottom:1px solid #eef0f2;min-width:0}
.api:last-child{border-bottom:none}
.api .name{min-width:0;flex:1 1 auto;overflow:hidden;text-overflow:ellipsis;
white-space:nowrap}
.api .num{flex:none;color:#656d76;font-size:13px;white-space:nowrap}
.api .acts{display:flex;flex:none;flex-wrap:nowrap;align-items:center;gap:8px;min-width:0}
/* The link used to be a stretched flex item, so its text sat at the top while
   the button's label was vertically centred. Give it the same box height and
   centre its text, so both labels share one baseline. */
.api .acts a{display:inline-flex;align-items:center;min-height:38px;
font:inherit;line-height:1.2;white-space:nowrap}
.api .acts button{min-height:38px;line-height:1.2}
.api .note{flex:1 1 100%;font-size:12.5px;overflow-wrap:anywhere}
.cpbox{flex:1 1 100%;-webkit-user-select:text;user-select:text}
button{border:1px solid #d5d9de;background:#fff;border-radius:6px;padding:7px 12px;
cursor:pointer;font:inherit;color:#1f2328;white-space:nowrap;max-width:100%}
button.primary{background:#4a63d8;border-color:#4a63d8;color:#fff;font-weight:500}
button.primary:hover{background:#3d54c0}
button:hover{border-color:#9aa4b2}
.meta{color:#656d76;font-size:13px;margin:6px 0 0;overflow-wrap:anywhere}
.ok{color:#1a7f37}.warn{color:#b42318}
#msg{margin-top:12px;font-size:13px;min-height:18px;overflow-wrap:anywhere}
.kv{color:#656d76;font-size:13px;overflow-wrap:anywhere}
.badge{display:inline-block;padding:1px 7px;border-radius:10px;font-size:12px;
background:#eef1f6;color:#4a5361}
/* In-page preview: a new window is blocked by the fnOS App WebView, so show
   the image in a lightbox inside this iframe instead. */
#pv{position:fixed;top:0;left:0;right:0;bottom:0;inset:0;z-index:9999;
display:flex;align-items:center;justify-content:center;padding:14px;
background:rgba(20,24,30,.74)}
#pv .card{background:#fff;border-radius:12px;width:100%;max-width:520px;
max-height:100%;display:flex;flex-direction:column;overflow:hidden;padding:0;
margin:0;border:1px solid #e3e6ea}
#pv .bar{display:flex;align-items:center;justify-content:space-between;gap:10px;
padding:10px 14px;border-bottom:1px solid #eef0f2;font-size:14px;min-width:0}
#pv .bar span{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
#pv .body{flex:1 1 auto;min-height:140px;display:flex;align-items:center;
justify-content:center;padding:12px;background:#f5f7fa;overflow:auto}
#pv img{max-width:100%;max-height:58vh;object-fit:contain;border-radius:6px}
#pv .err{color:#b42318;font-size:13px;overflow-wrap:anywhere;padding:8px}
#pv .foot{display:flex;flex-wrap:wrap;align-items:center;gap:8px;
padding:10px 14px;border-top:1px solid #eef0f2}
#pv .foot .u{flex:1 1 100%;font-size:12px;color:#656d76;overflow-wrap:anywhere}
@media(max-width:640px){
 .wrap{margin:16px auto 40px;padding:0 12px}
 .card{padding:14px 14px}
 h1{font-size:19px}
 .grid>div,.grid>div.sm,.grid>div.grow{flex:1 1 100%}
 .stats{gap:10px 12px}
 .api{gap:6px 8px}
 .api .acts{gap:6px}
 .api .acts button{padding:6px 9px;font-size:13px}
 .api .acts a{font-size:13px}
}
</style></head><body><div class="wrap">
<div class="head"><img src="$base/_icon" alt=""><h1>$title <span class="badge">v$version</span></h1></div>
<p class="sub">一个轻量的随机图片API 应用· 每个子文件夹就是一个独立随机图片接口</p>

<div class="card"><h2>运行状态</h2><div class="stats">
<div class="stat"><div class="k">图片根目录</div><div class="v"><code>$root</code></div></div>
<div class="stat"><div class="k">接口 / 图片</div><div class="v">$apicount 个接口 · $imgcount 张图片
<span class="kv">（扫描缓存 $ttl 秒）</span></div></div>
<div class="stat"><div class="k">网关入口</div><div class="v $gwclass">$gwstate</div></div>
<div class="stat"><div class="k">目录状态</div><div class="v $stateclass">$state</div></div>
</div></div>

<div class="card"><h2>设置</h2>
<div class="grid">
<div class="sm"><label for="f_port">服务端口</label><input id="f_port" type="number" min="1024" max="65535" value="$port"></div>
<div class="grow"><label for="f_root">图片根目录（留空 = 自动使用已授权目录）</label>
<input id="f_root" type="text" value="$root_value" placeholder="留空即自动跟随应用权限中授权的文件夹"></div>
<div class="sm"><label for="f_ttl">缓存秒数</label><input id="f_ttl" type="number" min="1" max="3600" value="$ttl"></div>
</div>
<div style="margin-top:14px"><button class="primary" id="save">保存并应用</button>
<button id="reload" style="margin-left:8px">立即刷新</button></div>
<p class="meta">桌面 / 手机入口走飞牛网关，改端口不影响图标；改图库路径即时生效。输入框显示的是当前生效路径；留空则自动使用应用权限里授权的文件夹，手动指定其它目录需先授权。「立即刷新」用于刚往图库加了图片、不想等缓存到期时清空清单缓存。</p>
<div id="msg"></div></div>

<div class="card"><h2>接口列表</h2><div class="apis">$rows</div></div>

<div class="card"><h2>使用说明</h2>
<p class="meta">目录结构：<code>图片根目录/分类名/*.jpg</code>，支持 jpg / jpeg / png / webp / gif / bmp / tiff，子目录可再嵌套。</p>
<p class="meta">新增接口：在图库里新建一个子文件夹并放入图片，最多等 $ttl 秒自动生效，无需重启。</p>
<p class="meta"><b>缓存秒数</b>（当前 $ttl 秒，可设 1–3600）：服务把「图库扫描结果（各分类的图片清单）」
在内存里保留这么久，到期才重新遍历目录。它<b>不缓存图片本身</b>，每次请求仍随机取一张并带
<code>no-store</code>；这个数值只影响新建分类 / 增删图片后多久生效。图库大、不常改动可调大（省磁盘扫描），
改动频繁可调小；保存设置或点设置区的「立即刷新」会立即清空缓存。</p>
<p class="meta">接口名<b>不区分大小写</b>：<code>/Wallpaper</code>、<code>/wallpaper</code>、<code>/WALLPAPER</code> 都指向同一个分类；若图库里同时存在仅大小写不同的文件夹，需使用精确名称。</p>
<p class="meta">自定义目录权限：应用以专用用户运行。<b>顶层文件夹</b>需到
<b>设置 → 应用管理 → RanPix → 权限设置</b> 授权；该列表只有共享文件夹，<b>选不到子目录</b>。
子文件夹显示「目录无读取权限」时，到 <b>文件管理 → 选中文件夹 → 详细信息 → 权限 → 高级</b>
启用继承父级权限（或在父目录上「重置子级权限」）。根目录能读不代表每个子目录都能读。</p>
<p class="meta">「打开看看」在当前页弹出预览；「复制地址」会<b>跟随当前访问的域名 / IP</b>，端口固定为免登录的服务端口 <code>$port</code>，
因此复制结果可粘贴到任意浏览器或第三方应用（中文接口名自动编码）；从网关入口复制时会自动把端口换成服务端口。</p>
<p class="meta">注意：<code>$gwurl</code> 是飞牛同源网关地址，只在已登录的桌面 / 手机 App 内有效；
直接外传会被飞牛统一鉴权拦截，显示 <code>invalid token</code>，所以「复制地址」不会给出这种地址。</p>
<p class="meta">接口列表 <a href="$base/_apis">/_apis</a> · 健康检查 <a href="$base/_health">/_health</a> ·
响应带 <code>no-store</code>，浏览器和 CDN 不会缓存，每次请求都是新的一张。</p>
</div></div>
<script>
var BASE='$base', GATEWAY=$gateway, DIRECT='$direct', PORT=$port;
function msg(t,c){var e=document.getElementById('msg');e.textContent=t;e.className=c||'';}
function gwUrl(p){return location.protocol+'//'+location.host+BASE+'/'+p;}
/* Shareable URL: follow whatever host the user is currently visiting, but
   always land on the token-free TCP port. A /app/<app>/ gateway URL only
   works inside an authenticated fnOS session and answers `invalid token`
   everywhere else. DIRECT (server-injected LAN address) is just a fallback
   for loopback / malformed hostnames. */
function directUrl(p){
  var h=location.hostname;
  if(!h||h==='127.0.0.1'||h==='localhost'||h==='::1'||h==='0.0.0.0')return DIRECT+'/'+p;
  if(h.indexOf(':')>=0&&h.charAt(0)!=='[')h='['+h+']';
  if(location.port===String(PORT))return location.origin+BASE+'/'+p;
  return location.protocol+'//'+h+':'+PORT+'/'+p;
}
/* In-app preview. The fnOS mobile App embeds us in an iframe/WebView that
   blocks target=_blank, so show the image in a lightbox inside this page.
   Gateway URL is tried first (same-origin, carries the App session); if it
   is rejected, fall back to the token-free LAN URL. */
var pvEl=null,pvP='',pvStage=0,pvSeq=0;
function pvClose(){if(pvEl&&pvEl.parentNode){pvEl.parentNode.removeChild(pvEl)}pvEl=null;}
function pvLoad(){
  var img=document.getElementById('pvImg'),err=document.getElementById('pvErr');
  pvStage=0;err.style.display='none';img.style.display='';
  pvSeq++;
  img.src=gwUrl(pvP)+'?_='+Date.now()+'-'+pvSeq;
  document.getElementById('pvUrl').textContent=directUrl(pvP);
}
function pvFail(){
  var img=document.getElementById('pvImg'),err=document.getElementById('pvErr');
  if(pvStage===0){pvStage=1;img.src=directUrl(pvP)+'?_='+Date.now()+'-'+pvSeq;return;}
  img.style.display='none';err.style.display='block';
  err.textContent='图片加载失败。请在与 NAS 同一网络的浏览器中打开这个直连地址：'+directUrl(pvP);
}
function pvShow(p){
  pvP=p;
  if(!pvEl){
    pvEl=document.createElement('div');pvEl.id='pv';
    pvEl.innerHTML='<div class="card"><div class="bar"><span id="pvTitle"></span>'+
      '<button id="pvX" type="button">关闭</button></div>'+
      '<div class="body"><img id="pvImg" alt=""><div id="pvErr" class="err" style="display:none"></div></div>'+
      '<div class="foot"><button id="pvNext" type="button">换一张</button>'+
      '<button id="pvCopy" class="cp" type="button">复制直连地址</button>'+
      '<div class="u" id="pvUrl"></div></div></div>';
    document.body.appendChild(pvEl);
    pvEl.addEventListener('click',function(e){if(e.target===pvEl)pvClose()});
    document.getElementById('pvX').onclick=pvClose;
    document.getElementById('pvNext').onclick=function(){pvLoad()};
    document.getElementById('pvImg').onerror=function(){pvFail()};
  }
  document.getElementById('pvTitle').textContent='/'+decodeURIComponent(p)+' · 随机一张';
  document.getElementById('pvCopy').setAttribute('data-p',p);
  pvLoad();
}
/* Copy buttons: delegated binding + clipboard API -> execCommand -> selectable box.
   The fnOS App embeds this page in an iframe where clipboard-write is often
   denied, so a silent Promise rejection must never leave the button dead. */
function copyUrl(btn){
  /* Copy the token-free, host-aware URL (see directUrl above). */
  var url=directUrl(btn.getAttribute('data-p')||'');
  var old=btn.textContent||'复制地址';
  function done(){btn.textContent='已复制';setTimeout(function(){btn.textContent=old},1600);}
  function legacy(){
    var ta=document.createElement('textarea');
    ta.value=url;ta.setAttribute('readonly','');
    ta.style.cssText='position:fixed;left:-9999px;top:0;opacity:0';
    document.body.appendChild(ta);ta.focus();ta.select();
    ta.setSelectionRange(0,url.length);
    var ok=false;try{ok=document.execCommand('copy')}catch(e){}
    document.body.removeChild(ta);return ok;
  }
  function manual(){
    var act=btn.parentNode,box=act.querySelector('.cpbox');
    if(!box){
      box=document.createElement('input');box.className='cpbox';box.type='text';
      box.readOnly=true;box.value=url;
      box.style.cssText='width:100%;min-width:0;border:1px solid #d5d9de;border-radius:6px;padding:6px 8px;font:12px monospace;color:#1f2328';
      act.appendChild(box);
    }
    box.style.display='block';box.focus();box.select();
    btn.textContent='长按上方地址复制';
    setTimeout(function(){btn.textContent=old},5000);
  }
  function fallback(){if(legacy()){done()}else{manual()}}
  if(navigator.clipboard&&navigator.clipboard.writeText){
    try{navigator.clipboard.writeText(url).then(done,fallback)}catch(e){fallback()}
  }else{fallback()}
}
document.addEventListener('click',function(e){
  var b=e.target;
  while(b&&b!==document){
    if(b.getAttribute){
      var p=b.getAttribute('data-p');
      if(p!==null&&p!==undefined){
        var cls=' '+(b.className||'')+' ';
        if(b.tagName==='A'&&cls.indexOf(' pv ')>=0){e.preventDefault();pvShow(p);return;}
        if(b.tagName==='BUTTON'&&cls.indexOf(' cp ')>=0){copyUrl(b);return;}
      }
    }
    b=b.parentNode;
  }
});
document.getElementById('save').onclick=function(){
  var btn=this;btn.disabled=true;msg('正在保存…');
  var body=new URLSearchParams({port:document.getElementById('f_port').value,
    image_root:document.getElementById('f_root').value,
    cache_ttl:document.getElementById('f_ttl').value});
  fetch(BASE+'/_config',{method:'POST',headers:{'Content-Type':'application/x-www-form-urlencoded'},body:body})
   .then(function(r){return r.json()}).then(function(j){
     btn.disabled=false;
     if(!j.ok){msg('保存失败：'+j.error,'warn');return;}
     if(j.restart){
       msg('端口已改为 '+j.port+'，正在重启服务…','ok');
       if(GATEWAY){setTimeout(function(){location.reload()},1800);}
       else{var u=location.protocol+'//'+location.hostname+':'+j.port+'/';
            setTimeout(function(){location.href=u},1600);}
     }else{
       msg('已保存，'+(j.message||'配置已生效'),'ok');
       setTimeout(function(){location.reload()},900);
     }
   }).catch(function(e){btn.disabled=false;msg('请求失败：'+e,'warn')});
};
document.getElementById('reload').onclick=function(){
  var btn=this;btn.disabled=true;msg('正在重新扫描图库…');
  fetch(BASE+'/_reload',{method:'POST'})
   .then(function(r){return r.json()}).then(function(j){
     btn.disabled=false;
     if(!j.ok){msg('刷新失败：'+(j.error||'未知错误'),'warn');return;}
     msg('已重新扫描，'+(j.restart?'服务正在重启':'缓存已清空'),'ok');
     setTimeout(function(){location.reload()},900);
   }).catch(function(e){btn.disabled=false;msg('请求失败：'+e,'warn')});
};
</script></body></html>""")


def index_page(host_header, cfg, base=""):
    cats = categories()
    st = root_status(cfg)
    rows = []
    for name in sorted([n for n in cats if n]):
        count = len(cats[name])
        err = _scan_errors.get(name)
        if err:
            acts = '<span class="kv">接口暂不可用</span>'
            note = ('<div class="note warn">目录无读取权限（%s）→ 请在 文件管理 → 详细信息 → '
                    '权限 → 高级 中启用继承父级权限（应用设置里无法单独授权子目录）</div>'
                    % html.escape(err))
        else:
            encoded = quote(name)
            acts = ('<a class="pv" href="%s/%s" data-p="%s" target="_blank">打开看看</a>'
                    '<button class="cp" data-p="%s">复制地址</button>'
                    % (html.escape(base), html.escape(encoded),
                       html.escape(encoded), html.escape(encoded)))
            note = ('<div class="note kv">目录为空，或没有 jpg / jpeg / png / webp / gif / bmp / tiff 图片</div>'
                    if count == 0 else "")
        rows.append(
            '<div class="api"><div class="name"><code>/%s</code></div>'
            '<div class="num">%d 张</div><div class="acts">%s</div>%s</div>'
            % (html.escape(name), count, acts, note)
        )
    if "" in cats:
        rows.append('<div class="api"><div class="name"><code>根目录散图</code></div>'
                    '<div class="num">%d 张</div>'
                    '<div class="acts kv">放在根目录下、不属于任何分类</div></div>'
                    % len(cats[""]))
    if not rows:
        rows.append('<div class="api kv">还没有找到图片。'
                    '在图片根目录里新建子文件夹并放入图片即可。</div>')
    stored = ""
    try:
        with open(CONFIG_PATH, "r", encoding="utf-8") as fh:
            stored = (json.load(fh).get("image_root") or "")
    except (OSError, ValueError):
        pass
    return PAGE.substitute(
        title=APP_TITLE, version=VERSION, port=cfg["port"],
        root=html.escape(cfg["image_root"]),
        # config.json is intentionally empty when the root is auto-detected
        # from fnOS TRIM_DATA_ACCESSIBLE_PATHS. Still show the effective path
        # in the input, otherwise the browser renders a misleading example.
        root_value=html.escape(stored or cfg["image_root"]),
        state=html.escape(st["hint"]),
        stateclass="ok" if st["readable"] and not _scan_errors else "warn",
        gwstate="已就绪" if GATEWAY_READY else "未启用（仅局域网直连可用）",
        gwclass="ok" if GATEWAY_READY else "warn",
        gwurl=GATEWAY_PREFIX + "/",
        direct=direct_base(cfg, host_header),
        base=base, gateway="true" if base else "false",
        apicount=len([n for n in cats if n]),
        imgcount=sum(len(v) for v in cats.values()),
        ttl=cfg["cache_ttl"], rows="\n".join(rows),
    ).encode("utf-8")


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "RanPix/" + VERSION

    def log_message(self, fmt, *args):
        log("%s %s" % (self.address_string(), fmt % args))

    def split_path(self):
        """Strip the fnOS gateway prefix and return (base_prefix, path)."""
        path = unquote(urlparse(self.path).path)
        lower = path.lower()
        prefix = GATEWAY_PREFIX.lower()
        if lower == prefix or lower.startswith(prefix + "/"):
            return GATEWAY_PREFIX, path[len(GATEWAY_PREFIX):] or "/"
        return "", path

    def _send(self, code, body, ctype, extra=None):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
        self.send_header("Pragma", "no-cache")
        for key, value in (extra or {}).items():
            self.send_header(key, value)
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(body)

    def send_json(self, obj, code=200):
        self._send(code, json.dumps(obj, ensure_ascii=False, indent=2).encode("utf-8"),
                   "application/json; charset=utf-8")

    def send_text(self, text, code=404):
        self._send(code, text.encode("utf-8"), "text/plain; charset=utf-8")

    def send_image(self, path):
        ext = os.path.splitext(path)[1].lower()
        try:
            size = os.path.getsize(path)
            fh = open(path, "rb")
        except OSError:
            return self.send_text("Image not readable.", 500)
        self.send_response(200)
        self.send_header("Content-Type", MIME.get(ext, "application/octet-stream"))
        self.send_header("Content-Length", str(size))
        self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
        self.send_header("Pragma", "no-cache")
        self.send_header("Expires", "0")
        self.end_headers()
        with fh:
            if self.command != "HEAD":
                try:
                    shutil.copyfileobj(fh, self.wfile, 262144)
                except (BrokenPipeError, ConnectionResetError):
                    pass

    def icon(self):
        here = os.path.dirname(os.path.abspath(__file__))
        for p in (os.path.join(here, "ui", "images", "icon_64.png"),
                  os.path.join(os.path.dirname(here), "ui", "images", "icon_64.png")):
            try:
                with open(p, "rb") as fh:
                    return self._send(200, fh.read(), "image/png")
            except OSError:
                continue
        return self.send_text("", 204)

    def handle_config(self, form):
        def val(key):
            return (form.get(key) or [""])[0].strip()
        cfg = load_config()
        old_port = cfg["port"]
        port = valid_port(val("port"))
        if not port:
            return self.send_json({"ok": False, "error": "端口需为 1024-65535 的数字"}, 400)
        root, err = valid_root(val("image_root"))
        if err:
            return self.send_json({"ok": False, "error": err}, 400)
        ttl = valid_ttl(val("cache_ttl")) or 30
        if port != old_port:
            s = socket.socket()
            try:
                s.bind(("0.0.0.0", port))
            except OSError:
                return self.send_json({"ok": False,
                                       "error": "端口 %d 已被占用，请换一个" % port}, 409)
            finally:
                s.close()
        new = {"image_root": root, "port": port, "cache_ttl": ttl}
        try:
            save_config(new)
        except OSError as exc:
            return self.send_json({"ok": False, "error": "配置写入失败：%s" % exc}, 500)
        _cache["ts"] = 0.0
        restart = port != old_port
        log("config saved: port=%d root=%s ttl=%d restart=%s"
            % (port, root or "(default share)", ttl, restart))
        if restart:
            schedule_execv()
        return self.send_json({
            "ok": True, "port": port,
            "image_root": root or detect_share(),
            "cache_ttl": ttl, "restart": restart,
            "message": "端口已修改，服务正在重启" if restart else "配置已保存并立即生效",
        })

    def handle_reload(self):
        cfg = load_config()
        if cfg["port"] != BOUND_PORT:
            s = socket.socket()
            try:
                s.bind(("0.0.0.0", cfg["port"]))
            except OSError:
                return self.send_json({"ok": False,
                                       "error": "端口 %d 已被占用" % cfg["port"]}, 409)
            finally:
                s.close()
            _cache["ts"] = 0.0
            schedule_execv()
            return self.send_json({"ok": True, "restart": True, "port": cfg["port"]})
        _cache["ts"] = 0.0
        return self.send_json({"ok": True, "restart": False, "port": BOUND_PORT})

    def route(self, path, base):
        cfg = load_config()
        if path == "/_icon":
            return self.icon()
        if path == "/_health":
            st = root_status(cfg)
            return self.send_json({"ok": True, "app": APPNAME, "version": VERSION,
                                  "port": cfg["port"], "image_root": cfg["image_root"],
                                  "root_readable": st["readable"],
                                  "gateway": GATEWAY_READY, "gateway_prefix": GATEWAY_PREFIX})
        if path == "/_apis":
            cats = categories()
            return self.send_json({
                "port": cfg["port"], "root": cfg["image_root"],
                "root_readable": root_status(cfg)["readable"],
                "apis": {("/" + n if n else "/"): len(cats[n]) for n in sorted(cats)},
                "total": sum(len(v) for v in cats.values()),
                "case_insensitive": True,
                "unreadable": {("/" + n): e for n, e in _scan_errors.items() if n},
                "root_error": _scan_errors.get("", ""),
            })
        if path == "/_config":
            return self.send_json({"ok": False, "error": "Use POST."}, 405)
        if path == "/" or path == "/index.html":
            return self._send(200, index_page(self.headers.get("Host", ""), cfg, base),
                              "text/html; charset=utf-8")
        name = path.lstrip("/")
        if not SAFE_NAME.match(name) or ".." in name or name.startswith("."):
            return self.send_text("Bad category name.", 400)
        cats = categories()
        canonical, ambiguous = resolve_category(name, cats)
        if ambiguous:
            return self.send_text(
                "Ambiguous API '%s'. Folders differ only by case, use an exact name: %s"
                % (name, ", ".join(sorted(ambiguous))), 409)
        if canonical is None:
            return self.send_text(
                "Unknown API '%s'. Available: %s (API names are case-insensitive)"
                % (name, ", ".join(sorted(n for n in cats if n)) or "(none)"), 404)
        if not cats[canonical]:
            err = _scan_errors.get(canonical)
            if err:
                return self.send_text(
                    "Category directory is not readable (%s). For a subfolder, use "
                    "fnOS File Manager > Details > Permissions > Advanced to enable "
                    "inheritance; the app permission list only covers top-level shares." % err, 403)
            return self.send_text("No images found in this category.", 404)
        return self.send_image(random.choice(cats[canonical]))

    def do_GET(self):
        try:
            base, path = self.split_path()
            self.route(path, base)
        except Exception as exc:
            log("ERROR %s: %s" % (self.path, exc))
            self.send_text("Internal error.", 500)

    def do_HEAD(self):
        self.do_GET()

    def do_POST(self):
        try:
            length = int(self.headers.get("Content-Length") or 0)
            raw = self.rfile.read(length).decode("utf-8") if length > 0 else ""
        except (ValueError, UnicodeDecodeError):
            raw = ""
        form = parse_qs(raw, keep_blank_values=True)
        _, path = self.split_path()
        try:
            if path == "/_config":
                return self.handle_config(form)
            if path == "/_reload":
                return self.handle_reload()
            return self.send_text("Not found.", 404)
        except Exception as exc:
            log("ERROR POST %s: %s" % (path, exc))
            return self.send_text("Internal error.", 500)


if hasattr(socket, "AF_UNIX") and hasattr(socketserver, "UnixStreamServer"):
    class UnixHTTPServer(socketserver.ThreadingMixIn, socketserver.UnixStreamServer):
        """HTTP over the fnOS gateway Unix socket."""
        daemon_threads = True
        allow_reuse_address = True

        def get_request(self):
            conn, _ = super().get_request()
            return conn, ("unix", 0)
else:                                     # e.g. local development on Windows
    UnixHTTPServer = None


def start_gateway():
    global GATEWAY_READY
    if UnixHTTPServer is None:
        log("gateway skipped: AF_UNIX unavailable")
        return None
    try:
        if os.path.lexists(SOCKET_PATH):
            os.unlink(SOCKET_PATH)
        srv = UnixHTTPServer(SOCKET_PATH, Handler)
        try:
            os.chmod(SOCKET_PATH, 0o666)   # nginx / app-center gateway must connect
        except OSError:
            pass
        GATEWAY_READY = True
        log("gateway socket ready: %s" % SOCKET_PATH)
        return srv
    except OSError as exc:
        log("gateway socket failed: %s" % exc)
        return None


def main():
    global BOUND_PORT
    cfg = load_config()
    BOUND_PORT = cfg["port"]
    st = root_status(cfg)
    log("starting RanPix v%s port=%s root=%s readable=%s py=%s"
        % (VERSION, cfg["port"], cfg["image_root"], st["readable"], sys.version.split()[0]))
    tcp = ThreadingHTTPServer(("0.0.0.0", cfg["port"]), Handler)
    tcp.daemon_threads = True
    unix = start_gateway()
    if unix:
        threading.Thread(target=unix.serve_forever,
                         kwargs={"poll_interval": 0.5}, daemon=True).start()
    try:
        tcp.serve_forever(poll_interval=0.5)
    except KeyboardInterrupt:
        pass
    finally:
        tcp.server_close()
        if unix:
            unix.server_close()
            try:
                os.unlink(SOCKET_PATH)
            except OSError:
                pass
        log("stopped")


if __name__ == "__main__":
    main()
