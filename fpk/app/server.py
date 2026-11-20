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
import queue
import random
import re
import shutil
import socket
import socketserver
import ssl
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from string import Template
from urllib.parse import parse_qs, quote, unquote, urlencode, urlparse

APPNAME = "ranpix"
APP_TITLE = "RanPix"
VERSION = "2.1.10"
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
        return "", "目录不可读：%s。本次设置未保存（授权方法见「使用说明」）" % (
            exc.strerror or "权限不足")
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


# Global deletion blacklist. A wallhaven ID added here is skipped by every
# collection task, regardless of category; the file lives beside config.json
# in ETC_DIR so it survives app updates and is shared across all tasks.
BLACKLIST_PATH = os.path.join(ETC_DIR, "blacklist.json")
_blacklist_lock = threading.RLock()


def image_wid(path):
    """Return the wallhaven id from a stored filename.

    Collected files are named wallhaven-<id>.<ext> and downloaded.txt stores
    the bare <id>; both match the API item's `id` used by the collector.
    """
    stem = os.path.splitext(os.path.basename(path))[0]
    if stem.lower().startswith("wallhaven-"):
        return stem[len("wallhaven-"):].strip().lower()
    return ""


def load_blacklist():
    with _blacklist_lock:
        try:
            with open(BLACKLIST_PATH, "r", encoding="utf-8") as fh:
                data = json.load(fh)
            if isinstance(data, dict):
                data = data.get("ids")
            if isinstance(data, list):
                return {str(x).strip().lower() for x in data if str(x).strip()}
        except (OSError, ValueError):
            pass
        return set()


def save_blacklist(ids):
    with _blacklist_lock:
        tmp = BLACKLIST_PATH + ".tmp"
        with open(tmp, "w", encoding="utf-8") as fh:
            json.dump({"ids": sorted(ids)}, fh, ensure_ascii=False, indent=2)
        os.replace(tmp, BLACKLIST_PATH)
        try:
            os.chmod(BLACKLIST_PATH, 0o666)
        except OSError:
            pass


def add_blacklist(wid):
    wid = str(wid or "").strip().lower()
    if not wid:
        return False
    with _blacklist_lock:
        ids = load_blacklist()
        if wid in ids:
            return False
        ids.add(wid)
        save_blacklist(ids)
    return True


def sweep_missing_blacklist():
    """Magic sweep: blacklist IDs whose image was deleted outside RanPix.

    When the user removes a collected file via the file manager (or any other
    means), the ID is still listed in that category's downloaded.txt. On the
    next collection run that ID would be skipped only for that one folder;
    this sweep records it in the GLOBAL blacklist so every task skips it.

    Collected files are named wallhaven-<id>.<ext> and downloaded.txt holds
    the bare <id>. Any recorded ID with no surviving matching file is treated
    as manually deleted. Returns (ok, payload).
    """
    _cache["ts"] = 0.0                  # force rescan to see external deletions
    cfg = load_config()
    root = cfg["image_root"]
    cats = categories()
    scanned = 0
    missing = set()
    for name, paths in cats.items():
        folder = os.path.join(root, name) if name else root
        state = os.path.join(folder, "downloaded.txt")
        try:
            with open(state, "r", encoding="utf-8") as fh:
                recorded = {line.strip().lower() for line in fh if line.strip()}
        except OSError:
            continue
        if not recorded:
            continue
        scanned += len(recorded)
        present = {image_wid(p) for p in paths}
        present.discard("")
        missing |= (recorded - present)

    added = 0
    for wid in sorted(missing):
        if add_blacklist(wid):
            added += 1
    log("magic sweep: %d recorded IDs, %d missing, %d newly blacklisted"
        % (scanned, len(missing), added))
    return True, {"ok": True, "scanned": scanned, "missing": len(missing),
                  "added": added, "total": len(load_blacklist())}


def delete_preview_image(category, index):
    """Delete the image shown at `index` in the preview's mtime-desc order.

    Mirrors the `order=recent&i=N` lookup in route() exactly so what the user
    sees is what gets removed. Returns (ok, payload).
    """
    cats = categories()
    canonical, _amb = resolve_category(category, cats)
    if canonical is None or not cats.get(canonical):
        return False, "分类不存在或无图片"
    ordered = sorted(cats[canonical], key=lambda p: (_mtime_of(p), p), reverse=True)
    if not ordered:
        return False, "分类无图片"
    idx = index % len(ordered)          # preview wraps around at the end
    target = ordered[idx]
    wid = image_wid(target)
    name = os.path.basename(target)
    try:
        os.unlink(target)
    except OSError as exc:
        return False, "删除失败：%s" % exc
    if wid:
        add_blacklist(wid)
    _cache["ts"] = 0.0                  # refresh gallery scan immediately
    log("deleted image: %s (wid=%s or empty)" % (target, wid or "n/a"))
    return True, {"ok": True, "deleted": name, "wid": wid,
                  "blacklisted": bool(wid)}


def _mtime_of(p):
    try:
        return os.path.getmtime(p)
    except OSError:
        return 0.0


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


# ---------------------------------------------------------------------------
# Wallhaven collector (stage 1)
#
# Ported from the user's Wallhaven-Downloader-CN bash scripts, but using only
# the Python standard library so the fpk stays dependency-free. The API v1
# response already carries `path`, `favorites` and `file_size`, so we no
# longer need wget --spider / jq / shuf.
# ---------------------------------------------------------------------------

FETCH_DEFAULTS = {
    # api_key is global (fetch.json); kept here only for legacy task configs.
    "api_key": "",
    "target": "Wallhaven",
    "count": 24,
    "categories": "111",       # general / anime / people bitmask
    "purity": "100",           # sfw / sketchy / nsfw bitmask
    "ratios": "",              # "" = any; e.g. landscape,portrait,16x9
    "sorting": "hot",          # hot / toplist / favorites / views
    "short_edge": 0,           # >= px on the short side; 0 = any
    "start_page": 0,           # 0 = random page
    "end_page": 0,             # 0 = unlimited (capped by API last_page)
    "min_favorites": 0,        # 0 = any
    "min_size_kb": 0,          # 0 = any
    "max_size_mb": 0,          # 0 = any
    "query": "",
    "clear_before": 0,         # 1 = empty the target category folder before collecting
    "max_pages": 500,          # internal safety cap
}
# Values the Wallhaven API actually honours. The three UI group names
# (wide/ultrawide/square) were never valid API params; they are now expanded
# into concrete ratios below so old tasks keep working after the UI change.
VALID_RATIOS = ("landscape", "portrait",
                "16x9", "16x10", "3x2", "4x3", "5x4",
                "21x9", "32x9", "48x9",
                "9x16", "10x16", "9x18", "1x1")
RATIO_ALIAS = {
    "wide": "16x9,16x10,3x2,4x3,5x4",
    "ultrawide": "21x9,32x9,48x9",
    "square": "1x1",                    # old "正方形" value -> real API value
}
VALID_SORTING = ("hot", "toplist", "favorites", "views")
FETCH_CONFIG_PATH = os.path.join(ETC_DIR, "fetch.json")
WH_API = "https://wallhaven.cc/api/v1/search"
WH_UA = ("Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
         "(KHTML, like Gecko) Chrome/120.0 Safari/537.36")

_fetch_lock = threading.Lock()
_cancel = threading.Event()
_fetch_state = {
    "running": False, "phase": "idle", "done": 0, "total": 0,
    "page": 0, "error": "", "started": 0, "finished": 0,
    "target": "", "log": [],
}


def load_fetch_config():
    cfg = dict(FETCH_DEFAULTS)
    try:
        with open(FETCH_CONFIG_PATH, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        if isinstance(data, dict):
            cfg.update({k: v for k, v in data.items() if k in cfg})
    except (OSError, ValueError):
        pass
    return cfg


def save_fetch_config(cfg):
    clean = {}
    for key, default in FETCH_DEFAULTS.items():
        clean[key] = cfg.get(key, default)
    with open(FETCH_CONFIG_PATH, "w", encoding="utf-8") as fh:
        json.dump(clean, fh, ensure_ascii=False, indent=2)
    try:
        os.chmod(FETCH_CONFIG_PATH, 0o600)
    except OSError:
        pass


def fetch_valid(cfg):
    """Validate and coerce a user-submitted collector config."""
    out = dict(FETCH_DEFAULTS)
    out["api_key"] = str(cfg.get("api_key") or "").strip()
    target = str(cfg.get("target") or "").strip()
    if not target or not SAFE_NAME.match(target) or ".." in target or target.startswith("."):
        return None, "目标分类名不合法（不能含 / \\ 或以 . 开头）"
    out["target"] = target
    for key, lo, hi in (("count", 1, 200), ("min_favorites", 0, 100000),
                        ("min_size_kb", 0, 102400), ("max_size_mb", 0, 2000),
                        ("max_pages", 1, 500), ("short_edge", 0, 10000),
                        ("start_page", 0, 500), ("end_page", 0, 500)):
        raw = cfg.get(key)
        try:
            val = int(raw) if raw not in (None, "") else out[key]
        except (TypeError, ValueError):
            return None, "%s 必须是数字" % key
        if not lo <= val <= hi:
            return None, "%s 需在 %d-%d 之间" % (key, lo, hi)
        out[key] = val
    if out["start_page"] and out["end_page"] and out["start_page"] > out["end_page"]:
        return None, "起始页码不能大于结束页码"
    if (out["max_size_mb"] and out["min_size_kb"]
            and out["max_size_mb"] * 1024 <= out["min_size_kb"]):
        return None, "文件大小上限必须大于下限"
    for key in ("categories", "purity"):
        val = str(cfg.get(key) or out[key])
        if len(val) != 3 or any(c not in "01" for c in val) or "1" not in val:
            return None, "%s 至少启用一项（3 位 0/1 组合）" % key
        out[key] = val
    ratios = [x.strip().lower() for x in str(cfg.get("ratios") or "").split(",")]
    expanded = []
    for r in ratios:
        if not r:
            continue
        # Migrate legacy UI group names to concrete API ratios.
        for part in RATIO_ALIAS.get(r, r).split(","):
            if part and part not in expanded:
                expanded.append(part)
    for r in expanded:
        if r not in VALID_RATIOS:
            return None, "比例不支持：%s" % r
    out["ratios"] = ",".join(expanded)
    sorting = str(cfg.get("sorting") or out["sorting"]).strip().lower()
    if sorting not in VALID_SORTING:
        return None, "排序方式不支持（可用：热门/最近一周/收藏量/浏览量）"
    out["sorting"] = sorting
    out["query"] = str(cfg.get("query") or "").strip()[:120]
    out["clear_before"] = 1 if str(cfg.get("clear_before") or "").strip().lower() \
        in ("1", "true", "on", "yes") else 0
    return out, ""


def apply_global_key(cfg):
    """Use the global API key; without one, Wallhaven only serves SFW content.

    This is the single enforcement point for the table's rule
    "API Key 留空则仅下载 SFW": sketchy/NSFW purity is silently collapsed to
    SFW at save time and again just before a job runs, so an old task can
    never download NSFW after the key is cleared.
    """
    key = ""
    try:
        with open(FETCH_CONFIG_PATH, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        if isinstance(data, dict):
            key = str(data.get("api_key") or "").strip()
    except (OSError, ValueError):
        pass
    cfg["api_key"] = key
    if not key:
        cfg["purity"] = "100"
    return cfg


# ---------------------------------------------------------------------------
# Image compression task config. Reuses the same task/scheduler/worker as the
# Wallhaven collector; only the job body differs (compress_images below).
# All paths are absolute and configurable because the app user may not have
# access to the paths hard-coded in the original compress.sh.
# ---------------------------------------------------------------------------
COMPRESS_DEFAULTS = {
    "src_dir": "/vol2/1000/Media/Wallhaven",          # images to compress (this dir only)
    "backup_dir": "/vol2/1000/Media/Image/Wall-Backup",  # original full-quality copies
    "max_height": 2160,        # resize short-edge ceiling (kept key name for compatibility); 0 = no resize
    "max_size_mb": 5,          # file size ceiling in MB; 0 = no size compression
    "q_max": 98,               # highest JPEG quality while shrinking size
    "q_min": 85,               # lowest JPEG quality (detail floor)
    "to_jpg": 1,               # convert non-JPG formats to JPG
    "recursive": 0,            # 1 = include subdirectories
}
COMPRESS_FORMATS = (".jpg", ".jpeg", ".png", ".bmp", ".tiff")
_COMPRESS_TOOLS = None        # lazily detected: ffmpeg / ffprobe (system bundled)


def compress_valid(cfg):
    """Validate and coerce a user-submitted compression config."""
    out = dict(COMPRESS_DEFAULTS)
    for key in ("src_dir", "backup_dir"):
        raw = os.path.normpath(str(cfg.get(key) or "").strip())
        if not raw or not os.path.isabs(raw):
            return None, "%s 必须是绝对路径" % ("源目录" if key == "src_dir" else "备份目录")
        if raw in FORBIDDEN_ROOTS or raw.startswith("/etc/") or raw.startswith("/proc/"):
            return None, "出于安全考虑，不允许使用系统目录作为%s" % (
                "源目录" if key == "src_dir" else "备份目录")
        out[key] = raw
    for key, lo, hi in (("max_height", 0, 20000), ("max_size_mb", 0, 2000),
                        ("q_max", 1, 100), ("q_min", 1, 100)):
        raw = cfg.get(key)
        try:
            val = int(raw) if raw not in (None, "") else out[key]
        except (TypeError, ValueError):
            return None, "%s 必须是数字" % key
        if not lo <= val <= hi:
            return None, "%s 需在 %d-%d 之间" % (key, lo, hi)
        out[key] = val
    if out["q_min"] > out["q_max"]:
        return None, "质量下限不能高于上限"
    for key in ("to_jpg", "recursive"):
        out[key] = 1 if str(cfg.get(key, out[key])).strip() in ("1", "true", "on", "yes") else 0
    return out, ""


def compress_tools():
    """Return (ffmpeg, ffprobe) paths; cached. Both ship with fnOS mediasrv."""
    global _COMPRESS_TOOLS
    if _COMPRESS_TOOLS is None:
        import shutil as _sh
        _COMPRESS_TOOLS = (_sh.which("ffmpeg"), _sh.which("ffprobe"))
    return _COMPRESS_TOOLS


def _imq_to_qscale(q):
    """Map ImageMagick-style quality (1-100) to ffmpeg mjpeg -q:v (2-31).

    Measured on fnOS ffmpeg 8.1: the IJG quality ffmpeg produces tracks
    ``100 - qscale * 3.5`` closely, so the inverse gives an equivalent
    visual quality. Lower qscale = higher quality.
    """
    try:
        q = int(q)
    except (TypeError, ValueError):
        q = 85
    return max(2, min(31, int(round((100 - q) / 3.5))))


def _ffmpeg_decode_argv(ffmpeg, src):
    """ffmpeg argv prefix that decodes one frame of any supported image."""
    return [ffmpeg, "-v", "error", "-y", "-i", src, "-frames:v", "1"]


def wh_request(url, api_key="", timeout=25):
    headers = {"User-Agent": WH_UA, "Accept": "application/json, image/*"}
    if api_key:
        headers["X-API-Key"] = api_key
    req = urllib.request.Request(url, headers=headers)
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read()


def wh_search(page, cfg):
    params = {
        "page": page,
        "categories": cfg["categories"],
        "purity": cfg["purity"],
        "sorting": cfg["sorting"],
    }
    # "hot" is an intrinsic ranking; the API rejects `order` for it.
    if cfg["sorting"] != "hot":
        params["order"] = "desc"
    if cfg["sorting"] == "toplist":
        params["topRange"] = "1w"        # 最近一周 Toplist-LastWeek
    if cfg.get("short_edge"):
        # Wallhaven's atleast is a min width x min height. Using PxP is the
        # exact way to require "短边 ≥ P" without knowing each image's ratio.
        n = int(cfg["short_edge"])
        params["atleast"] = "%dx%d" % (n, n)
    if cfg.get("ratios"):
        params["ratios"] = cfg["ratios"]
    if cfg.get("query"):
        params["q"] = cfg["query"]
    raw = wh_request(WH_API + "?" + urlencode(params), cfg["api_key"])
    return json.loads(raw.decode("utf-8"))


def wh_fetch_image(item, cfg):
    """Download the full-size original only; never fall back to thumbnails.

    Wallhaven's API exposes two CDN sets: the original at w.wallhaven.cc
    (full resolution, matching the atleast/ratio filters) and thumbnails at
    th.wallhaven.cc (thumbs.original is ~300px, thumbs.large ~430px). A past
    fallback silently saved those thumbnails when the original CDN failed,
    producing tiny tens-of-KB files far below the configured minimum size.
    Fetching the original is now mandatory: on failure this raises and the
    caller skips the image instead of degrading quality.

    Returns (blob, filename, "原图") or raises the download error.
    """
    full = item.get("path") or ""
    if not full:
        raise ValueError("API 未返回原图地址")
    name = os.path.basename(unquote(urlparse(full).path))
    ext = os.path.splitext(name)[1].lower()
    if ext not in SUPPORTED or not SAFE_NAME.match(name):
        raise ValueError("原图文件名不合法：%s" % name)
    return wh_request(full, cfg["api_key"], timeout=45), name, "原图"


def _fetch_note(text, limit=80):
    """Append one line to the in-memory task log (also written by log())."""
    with _fetch_lock:
        lines = _fetch_state["log"]
        lines.append(text)
        if len(lines) > limit:
            del lines[:len(lines) - limit]
    log("fetch: " + text)


def _fetch_set(**kw):
    with _fetch_lock:
        _fetch_state.update(kw)


def _fetch_fail(message, ctx=None):
    """Finalise a job that failed before the main loop started."""
    note = ctx["note"] if ctx else _fetch_note
    setst = ctx["set"] if ctx else _fetch_set
    note("采集失败：" + message)
    setst(running=False, finished=time.time(), phase="error", error=message)


class _LegacyFetchCtx:
    """Adapter so wh_collect can drive the old global single-shot state."""
    def set(self, **kw):
        _fetch_set(**kw)

    def note(self, text):
        _fetch_note(text)

    def cancelled(self):
        return _cancel.is_set()

    def wait(self, sec):
        return _cancel.wait(sec)


def wh_collect(cfg, ctx=None):
    """Run one collection job. ctx may be a task-specific context providing
    set/note/cancelled/wait; defaults to the legacy global single-shot state."""
    ctx = ctx or _LegacyFetchCtx()
    setst, note = ctx.set, ctx.note
    root = load_config()["image_root"]
    dest = os.path.join(root, cfg["target"])
    try:
        os.makedirs(dest, exist_ok=True)
    except OSError as exc:
        _fetch_fail("无法创建目录 %s：%s" % (dest, exc), ctx)
        return
    if not os.access(dest, os.W_OK):
        _fetch_fail("目录不可写：%s。请到 文件管理 → 详细信息 → 权限 中给应用用户写入权限" % dest, ctx)
        return

    # Optional: empty the target category folder before this run. Only plain
    # files directly inside `dest` are removed (never subdirectories), so the
    # category stays intact. downloaded.txt is a plain file and is removed too,
    # giving this run a clean seen-set; the global blacklist is untouched.
    if cfg.get("clear_before"):
        removed = 0
        try:
            for entry in os.listdir(dest):
                path = os.path.join(dest, entry)
                if os.path.isfile(path) or os.path.islink(path):
                    os.unlink(path)
                    removed += 1
        except OSError as exc:
            _fetch_fail("清空目标目录失败：%s" % exc, ctx)
            return
        note("开始前已清空目标分类文件夹（删除 %d 个文件）" % removed)

    state_file = os.path.join(dest, "downloaded.txt")
    seen = set()
    try:
        with open(state_file, "r", encoding="utf-8") as fh:
            seen = {line.strip().lower() for line in fh if line.strip()}
    except OSError:
        pass
    # Global deletion blacklist: images removed in the preview are recorded by
    # wallhaven id here and must be skipped by every task, in any category.
    blacklist = load_blacklist()
    skipped_blacklist = [0]

    setst(target=dest, done=0, total=cfg["count"], page=0, error="")
    rng = "随机起始页"
    if cfg["start_page"]:
        rng = "第 %d 页起" % cfg["start_page"]
    if cfg["end_page"]:
        rng += " 至第 %d 页" % cfg["end_page"]
    note("开始采集 → %s（目标 %d 张，%s，按接口顺序下载）" % (dest, cfg["count"], rng))

    try:
        first = wh_search(1, cfg)
        last = int((first.get("meta") or {}).get("last_page") or 1)
    except Exception as exc:
        _fetch_fail("访问 wallhaven API 失败：%s" % exc, ctx)
        return
    if cfg["end_page"]:
        last = min(last, cfg["end_page"])
    last = max(1, min(last, cfg["max_pages"]))
    # The start page is chosen exactly once: a non-zero start_page is used
    # verbatim; 0 means pick ONE random page. From there on, pages increase
    # sequentially and images follow the API's returned order.
    first_page = cfg["start_page"] or random.randint(1, last)
    if first_page > last:
        note("起始页 %d 超出可用范围，改从第 %d 页开始" % (first_page, last))
        first_page = last
    first_page = max(1, first_page)
    note("起始第 %d 页，可用页数 1-%d（第 1 页探测，安全上限 %d）"
         % (first_page, last, cfg["max_pages"]))

    min_size = cfg["min_size_kb"] * 1024
    max_size = cfg["max_size_mb"] * 1024 * 1024 if cfg["max_size_mb"] else float("inf")
    done = 0
    next_page = first_page
    rate_limited = 0

    try:
        while done < cfg["count"] and not ctx.cancelled() and next_page <= last:
            page = next_page
            setst(page=page)
            note("抓取第 %d 页…" % page)
            try:
                data = wh_search(page, cfg)
                rate_limited = 0
            except urllib.error.HTTPError as exc:
                if exc.code == 429:
                    rate_limited += 1
                    note("触发限流 429，冷却 30 秒（第 %d 次）" % rate_limited)
                    if ctx.wait(30) or rate_limited >= 5:
                        if rate_limited >= 5:
                            note("连续限流过多，停止采集")
                        break
                    continue                   # keep next_page: retry same page
                note("第 %d 页请求失败 HTTP %s，跳过" % (page, exc.code))
                next_page = page + 1
                continue
            except Exception as exc:
                note("第 %d 页请求失败 %s，跳过" % (page, exc))
                next_page = page + 1
                continue
            next_page = page + 1

            # Keep the API's order: "start at page 5" means page 5's first
            # image first. Previously random.shuffle() broke this guarantee.
            items = list(data.get("data") or [])
            for it in items:
                if done >= cfg["count"] or ctx.cancelled():
                    break
                fav = it.get("favorites") or 0
                if fav < cfg["min_favorites"]:
                    continue
                size = it.get("file_size") or 0
                if size and not min_size <= size <= max_size:
                    continue
                wid = it.get("id") or ""
                wl = wid.strip().lower()
                if not wl or wl in seen or wl in blacklist:
                    if wl in blacklist:
                        skipped_blacklist[0] += 1
                    continue

                tmp = ""
                try:
                    blob, name, label = wh_fetch_image(it, cfg)
                    # Only originals are downloaded now; guard against a
                    # truncated/placeholder response slipping into the library.
                    if len(blob) > max_size or len(blob) < 2048:
                        note("跳过 %s（实际 %d 字节不符）" % (name, len(blob)))
                        continue
                    if os.path.exists(os.path.join(dest, name)):
                        seen.add(wid)
                        continue
                    tmp = os.path.join(dest, "." + name + ".part")
                    with open(tmp, "wb") as fh:
                        fh.write(blob)
                    os.replace(tmp, os.path.join(dest, name))
                except urllib.error.HTTPError as exc:
                    if exc.code == 429 and not ctx.wait(30):
                        note("下载遇到 429，已等待 30 秒")
                    note("下载失败 %s：HTTP %s" % (wid, exc.code))
                    continue
                except Exception as exc:
                    note("下载失败 %s：%s" % (wid, exc))
                    continue
                finally:
                    if tmp:
                        try:
                            if os.path.exists(tmp):
                                os.unlink(tmp)
                        except OSError:
                            pass
                seen.add(wl)
                try:
                    with open(state_file, "a", encoding="utf-8") as fh:
                        fh.write(wid + "\n")
                except OSError:
                    pass
                done += 1
                setst(done=done)
                note("已下载 %d/%d：%s（%s，%d KB，收藏 %s）"
                            % (done, cfg["count"], name, label, len(blob) // 1024, fav))
    finally:
        _cache["ts"] = 0.0
        cancelled = ctx.cancelled()
        setst(running=False, finished=time.time(),
                   phase="cancelled" if cancelled else "done",
                   error="" if done or cancelled else "没有找到符合条件的图片，可放宽筛选条件")
        extra = ("；黑名单跳过 %d 张" % skipped_blacklist[0]) if skipped_blacklist[0] else ""
        note("采集结束，共 %d 张%s；接口列表已刷新" % (done, extra))


def _run_tool(argv, timeout=180):
    """Run an image tool; return (ok, stdout). Never raises."""
    try:
        p = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           timeout=timeout)
        return p.returncode == 0, (p.stdout or b"").decode("utf-8", "replace").strip()
    except (OSError, subprocess.SubprocessError) as exc:
        return False, str(exc)


def _img_dims(ffprobe, path):
    """Return (width, height) via ffprobe; (0, 0) when unreadable."""
    ok, out = _run_tool([ffprobe, "-v", "error", "-select_streams", "v:0",
                         "-show_entries", "stream=width,height",
                         "-of", "csv=p=0", path], timeout=30)
    if not ok:
        return 0, 0
    try:
        parts = (out or "").splitlines()[0].strip().split(",")
        return int(parts[0]), int(parts[1])
    except (ValueError, IndexError):
        return 0, 0


def _img_height(ffprobe, path):
    return _img_dims(ffprobe, path)[1]


def _size_kb(path):
    try:
        return (os.path.getsize(path) + 1023) // 1024
    except OSError:
        return 0


def compress_images(cfg, ctx=None):
    """Compress one directory in place using the system ffmpeg / ffprobe.

    Steps per image: backup original -> decode original once, scale tall
    images by height -> encode to JPG at a quality mapped from the 1-100
    setting -> step down quality (re-encoding from the ORIGINAL each time,
    never from a previous lossy pass) until the size ceiling is met ->
    atomic replace -> drop the original non-JPG file. Files already within
    every limit are left untouched. Fully cancellable via ctx.
    """
    ctx = ctx or _LegacyFetchCtx()
    setst, note = ctx.set, ctx.note
    ffmpeg, ffprobe = compress_tools()
    if not ffmpeg or not ffprobe:
        _fetch_fail("未找到 ffmpeg（ffmpeg / ffprobe），无法压缩", ctx)
        return

    src = cfg["src_dir"]
    backup = cfg["backup_dir"]
    if not os.path.isdir(src):
        _fetch_fail("源目录不存在或无权限：%s" % src, ctx)
        return
    if not os.access(src, os.R_OK | os.W_OK):
        _fetch_fail("源目录不可读写：%s。请到 设置 → 应用管理 → RanPix → 权限设置 授权该目录" % src, ctx)
        return
    try:
        os.makedirs(backup, exist_ok=True)
    except OSError as exc:
        _fetch_fail("无法创建备份目录 %s：%s" % (backup, exc), ctx)
        return
    if not os.access(backup, os.W_OK):
        _fetch_fail("备份目录不可写：%s。请先在应用权限设置里授权" % backup, ctx)
        return

    max_h = cfg["max_height"]
    max_kb = cfg["max_size_mb"] * 1024 if cfg["max_size_mb"] else 0
    qs_best = _imq_to_qscale(cfg["q_max"])    # higher quality -> smaller qscale
    qs_worst = _imq_to_qscale(cfg["q_min"])   # quality floor -> larger qscale
    if qs_best > qs_worst:
        qs_best, qs_worst = qs_worst, qs_best
    to_jpg = bool(cfg["to_jpg"])
    tmpdir = os.path.join(src, ".image_compress_tmp")
    try:
        os.makedirs(tmpdir, exist_ok=True)
    except OSError as exc:
        _fetch_fail("无法创建临时目录：%s" % exc, ctx)
        return

    # Gather candidate files (this directory, optionally recursive).
    files = []
    try:
        if cfg["recursive"]:
            for root, _dirs, names in os.walk(src):
                if os.path.abspath(root).startswith(os.path.abspath(tmpdir)):
                    continue
                for n in names:
                    p = os.path.join(root, n)
                    if os.path.splitext(n)[1].lower() in COMPRESS_FORMATS:
                        files.append(p)
        else:
            with os.scandir(src) as it:
                for e in it:
                    if e.is_file() and os.path.splitext(e.name)[1].lower() in COMPRESS_FORMATS:
                        files.append(e.path)
    except OSError as exc:
        _fetch_fail("扫描目录失败：%s" % exc, ctx)
        return
    files.sort()
    setst(target=src, done=0, total=len(files), page=0, error="")
    note("开始压缩：%s（共 %d 张候选，短边≤%s，体积≤%s，编码 ffmpeg）"
         % (src, len(files), max_h or "不限", (str(cfg["max_size_mb"]) + "MB") if max_kb else "不限"))

    done = 0
    skipped = 0
    failed = 0
    saved_kb = 0
    try:
        for idx, path in enumerate(files):
            if ctx.cancelled():
                break
            name = os.path.basename(path)
            ext = os.path.splitext(name)[1].lower()
            is_jpg = ext in (".jpg", ".jpeg")
            if not is_jpg and not to_jpg:
                skipped += 1
                continue

            width, height = _img_dims(ffprobe, path)
            size_kb = _size_kb(path)
            if not height or not width or not size_kb:
                note("跳过无效图片：%s" % name)
                skipped += 1
                continue
            short_edge = min(width, height)
            need = (max_h and short_edge > max_h) or (max_kb and size_kb > max_kb) or (not is_jpg)
            if not need:
                skipped += 1
                continue

            note("处理 %d/%d：%s（%dx%d，%dKB，%s）" %
                 (idx + 1, len(files), name, width, height, size_kb, ext.lstrip(".").upper()))
            base = os.path.splitext(name)[0]
            final = os.path.join(os.path.dirname(path), base + ".jpg")
            if os.path.abspath(final) == os.path.abspath(path):
                final = path
            work = os.path.join(tmpdir, base + ".work.jpg")
            try:
                if os.path.exists(work):
                    os.unlink(work)
            except OSError:
                pass

            # 1) backup original (once, keeps original format & full detail)
            bpath = os.path.join(backup, name)
            if not os.path.exists(bpath):
                try:
                    shutil.copy2(path, bpath)
                except OSError as exc:
                    note("备份失败，跳过：%s（%s）" % (name, exc))
                    failed += 1
                    continue

            # Scale by SHORT EDGE (the smaller of width/height) when it exceeds
            # the ceiling. Pin that short edge to the ceiling and let ffmpeg
            # derive the other side ("-2" keeps aspect ratio and rounds to an
            # even number, required by JPEG yuv420p).
            vf = None
            if max_h and short_edge > max_h:
                edge = (max_h // 2) * 2 or 2
                if height <= width:          # landscape: height is the short edge
                    vf = "scale=-2:%d" % edge
                else:                        # portrait: width is the short edge
                    vf = "scale=%d:-2" % edge

            def encode(qscale):
                # Always decode from the ORIGINAL file so repeated passes never
                # stack lossy re-encoding artifacts on top of each other.
                argv = _ffmpeg_decode_argv(ffmpeg, path)
                if vf:
                    argv += ["-vf", vf]
                argv += ["-q:v", str(qscale), work]
                return _run_tool(argv, timeout=180)

            # 2) first encode at the best mapped quality
            ok, err = encode(qs_best)
            if not ok or not _size_kb(work):
                note("编码 JPG 失败，跳过：%s（%s）" % (name, (err or "")[:60]))
                failed += 1
                continue

            # 3) step down quality while the file is still over the size cap
            if max_kb:
                q = qs_best
                while _size_kb(work) > max_kb and q < qs_worst:
                    q += 1
                    ok2, err2 = encode(q)
                    if not ok2 or not _size_kb(work):
                        break

            new_kb = _size_kb(work)
            if not new_kb:
                note("压缩结果无效，跳过：%s" % name)
                failed += 1
                continue
            try:
                os.replace(work, final)
            except OSError as exc:
                note("替换失败，跳过：%s（%s）" % (name, exc))
                failed += 1
                continue
            # 4) drop the original non-JPG file after a successful replace
            if not is_jpg and os.path.abspath(final) != os.path.abspath(path):
                try:
                    os.unlink(path)
                except OSError:
                    pass
            if new_kb < size_kb:
                saved_kb += size_kb - new_kb
            done += 1
            setst(done=done)
            nw, nh = _img_dims(ffprobe, final)
            note("完成：%s → %dx%d，%dKB（原 %dKB）" %
                 (os.path.basename(final), nw, nh, new_kb, size_kb))
    finally:
        try:
            shutil.rmtree(tmpdir, ignore_errors=True)
        except OSError:
            pass
        cancelled = ctx.cancelled()
        setst(running=False, finished=time.time(),
              phase="cancelled" if cancelled else "done",
              error="" if (done or cancelled or skipped) else "没有需要处理的文件")
        note("压缩结束：处理 %d 张，跳过 %d 张，失败 %d 张，共省 %.1f MB%s"
             % (done, skipped, failed, saved_kb / 1024.0, "（已取消）" if cancelled else ""))


# ---------------------------------------------------------------------------
# Scheduled collection tasks (task mode). All task definitions live in one
# JSON file; a single worker executes queued jobs serially so wallhaven is
# never hammered by overlapping requests. Zero third-party dependencies.
# ---------------------------------------------------------------------------
TASKS_PATH = os.path.join(ETC_DIR, "tasks.json")
_tasks_lock = threading.RLock()
_tasks = []                       # list of persisted task dicts
_task_rt = {}                     # task id -> runtime dict
_task_queue = queue.Queue()
_sched_stop = threading.Event()
_queued_today = set()              # (task id, YYYY-MM-DD) claimed by scheduler


def valid_time(value):
    m = re.match(r"^\s*(\d{1,2}):(\d{2})\s*$", str(value or ""))
    if not m:
        return ""
    h, mi = int(m.group(1)), int(m.group(2))
    if not (0 <= h <= 23 and 0 <= mi <= 59):
        return ""
    return "%02d:%02d" % (h, mi)


def new_task_id():
    return "t%d%03d" % (int(time.time()), random.randint(0, 999))


def task_rt(tid):
    with _tasks_lock:
        rt = _task_rt.get(tid)
        if rt is None:
            rt = {"running": False, "phase": "idle", "done": 0, "total": 0,
                  "page": 0, "log": [], "finished": 0, "started": 0,
                  "error": "", "target": "", "cancel": threading.Event()}
            _task_rt[tid] = rt
        return rt


def valid_days(value):
    """Weekday set: 1=Mon ... 7=Sun. Empty string means one-shot."""
    raw = str(value or "")
    return "".join(d for d in "1234567" if d in raw)


def load_tasks():
    global _tasks
    loaded = []
    try:
        with open(TASKS_PATH, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        items = data.get("tasks") if isinstance(data, dict) else data
        if isinstance(items, list):
            for it in items:
                if not isinstance(it, dict):
                    continue
                kind = str(it.get("type") or "fetch").strip()
                if kind not in ("fetch", "compress"):
                    kind = "fetch"           # legacy tasks have no type field
                if kind == "compress":
                    cfg, err = compress_valid(it.get("cfg") or {})
                else:
                    cfg, err = fetch_valid(it.get("cfg") or {})
                    if not err:
                        cfg = apply_global_key(cfg)
                if err:
                    continue
                tid = str(it.get("id") or "").strip() or new_task_id()
                try:
                    cnt = int(it.get("last_count") or 0)
                except (TypeError, ValueError):
                    cnt = 0
                # Migrate v1.3 tasks: loop=True -> every day, loop=False -> once.
                days = it.get("days")
                if days is None:
                    days = "1234567" if it.get("loop", True) else ""
                loaded.append({
                    "id": tid,
                    "type": kind,
                    "name": str(it.get("name") or "未命名任务").strip()[:60] or "未命名任务",
                    "enabled": bool(it.get("enabled", True)),
                    "time": valid_time(it.get("time")) or "03:00",
                    "days": valid_days(days),
                    "last_run": str(it.get("last_run") or ""),
                    "last_status": str(it.get("last_status") or "idle"),
                    "last_count": cnt,
                    "cfg": cfg,
                })
    except (OSError, ValueError):
        pass
    with _tasks_lock:
        _tasks = loaded
        for t in _tasks:
            task_rt(t["id"])


def save_tasks():
    with _tasks_lock:
        payload = {"tasks": [dict(t) for t in _tasks]}
    tmp = TASKS_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=2)
    os.replace(tmp, TASKS_PATH)
    try:
        os.chmod(TASKS_PATH, 0o600)   # may contain an API key
    except OSError:
        pass


def task_public(t, rt=None):
    rt = rt or task_rt(t["id"])
    cfg = t["cfg"]
    kind = t.get("type", "fetch")
    if kind == "compress":
        pub_cfg = {k: cfg.get(k, v) for k, v in COMPRESS_DEFAULTS.items()}
        target, count = cfg["src_dir"], 0
    else:
        # Full filter config for the edit form; never echo back the API key.
        pub_cfg = {k: cfg.get(k, v) for k, v in FETCH_DEFAULTS.items() if k != "api_key"}
        target, count = cfg["target"], cfg["count"]
    return {
        "id": t["id"], "type": kind, "name": t["name"], "enabled": t["enabled"],
        "time": t["time"], "days": t.get("days", ""),
        "loop": bool(t.get("days", "")),   # kept for older clients
        "last_run": t["last_run"], "last_status": t["last_status"],
        "last_count": t["last_count"],
        "cfg": pub_cfg,
        "target": target, "count": count,
        "running": rt["running"], "phase": rt["phase"],
        "done": rt["done"], "total": rt["total"], "page": rt["page"],
        "error": rt["error"], "finished": rt["finished"],
        "log": list(rt["log"]),
    }


class _TaskFetchCtx:
    """wh_collect context bound to one task's runtime state."""
    def __init__(self, tid):
        self.tid = tid
        self.rt = task_rt(tid)

    def set(self, **kw):
        with _tasks_lock:
            self.rt.update(kw)

    def note(self, text):
        with _tasks_lock:
            lines = self.rt["log"]
            lines.append(text)
            if len(lines) > 80:
                del lines[:len(lines) - 80]
        log("task[%s] %s" % (self.tid, text))

    def cancelled(self):
        return self.rt["cancel"].is_set()

    def wait(self, sec):
        return self.rt["cancel"].wait(sec)


def run_task_job(tid):
    """Execute one task in the single worker thread."""
    with _tasks_lock:
        t = next((x for x in _tasks if x["id"] == tid), None)
    if not t:
        return
    rt = task_rt(tid)
    kind = t.get("type", "fetch")
    cfg = t["cfg"]
    if kind == "compress":
        target0, total0 = cfg["src_dir"], 0   # totals filled after directory scan
    else:
        target0, total0 = cfg["target"], cfg["count"]
    with _tasks_lock:
        rt["cancel"].clear()
        rt.update(running=True, phase="running", done=0,
                  total=total0, page=0, error="",
                  started=time.time(), finished=0, target=target0, log=[])
    ctx = _TaskFetchCtx(tid)
    ctx.note("开始执行任务：%s（%s）" % (t["name"], t["time"]))
    try:
        if kind == "compress":
            compress_images(dict(cfg), ctx)
            _cache["ts"] = 0.0            # compressed files changed -> refresh APIs
        else:
            run_cfg = apply_global_key(dict(cfg))
            if not run_cfg["api_key"] and run_cfg["purity"] != "100":
                ctx.note("未填写 API Key，按规则强制仅下载 SFW")
            wh_collect(run_cfg, ctx)
    except Exception as exc:
        log("task[%s] unexpected error: %s" % (tid, exc))
        _fetch_fail("任务异常：%s" % exc, ctx)
    finally:
        phase = rt["phase"]
        if phase == "cancelled":
            status = "cancelled"
        elif phase == "error":
            status = "error"
        elif rt["done"]:
            status = "done"
        else:
            status = "empty"
        with _tasks_lock:
            t["last_run"] = time.strftime("%Y-%m-%d %H:%M")
            t["last_status"] = status
            t["last_count"] = rt["done"]
            if not t.get("days"):
                t["enabled"] = False          # one-shot: auto-disable after first run
            rt["running"] = False
        _cache["ts"] = 0.0
        save_tasks()


def _task_worker():
    while True:
        tid = _task_queue.get()
        try:
            run_task_job(tid)
        except Exception as exc:
            log("task worker error: %s" % exc)
        finally:
            _task_queue.task_done()


def _scheduler_loop():
    log("task scheduler started (weekday fixed-time, 20s tick)")
    while not _sched_stop.wait(20):
        try:
            now = time.localtime()
            hhmm = "%02d:%02d" % (now.tm_hour, now.tm_min)
            today = time.strftime("%Y-%m-%d")
            wd = str(now.tm_wday + 1)           # time.localtime: 0=Mon .. 6=Sun
            with _tasks_lock:
                due = []
                for t in _tasks:
                    if not t["enabled"]:
                        continue
                    if t["last_run"].startswith(today):
                        continue
                    if hhmm != t["time"]:        # only fire during the scheduled minute
                        continue
                    days = t.get("days", "")
                    if days and wd not in days:  # empty days = one-shot, any day
                        continue
                    key = (t["id"], today)
                    if key in _queued_today:
                        continue
                    _queued_today.add(key)
                    due.append(t["id"])
            for tid in due:
                _task_queue.put(tid)
                log("scheduler: queued task %s" % tid)
        except Exception as exc:
            log("scheduler error: %s" % exc)


def start_tasks():
    load_tasks()
    threading.Thread(target=_task_worker, daemon=True).start()
    threading.Thread(target=_scheduler_loop, daemon=True).start()



PAGE = Template("""<!doctype html><html lang="zh-CN"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1,user-scalable=no,viewport-fit=cover">
<title>$title · 随机图片 API</title><style>
:root{color-scheme:light;
--brand:#4a63d8;--ink:#1f2328;--muted:#656d76;--line:#e3e6ea;
--c-run:#2f7de1;--c-set:#0f9b8e;--c-api:#7a5af0;--c-wall:#e0703a;--c-zip:#2f9e66;--c-help:#8a94a3}
*{box-sizing:border-box}
html,body{max-width:100%;height:100%;overflow:hidden;overscroll-behavior-x:none}
body{margin:0;background:#f5f7fa;
color:var(--ink);-webkit-text-size-adjust:100%;touch-action:pan-y;
font:14px/1.6 -apple-system,BlinkMacSystemFont,"Segoe UI","Microsoft YaHei",sans-serif}
.wrap{max-width:920px;margin:26px auto 56px;padding:0 20px}
/* two-column shell: left nav + right content */
.layout{display:flex;gap:18px;max-width:1180px;height:100vh;height:100dvh;
margin:0 auto;padding:18px 20px;align-items:flex-start}
.side{width:196px;flex:0 0 196px;background:#fff;border:1px solid var(--line);border-radius:14px;
 box-shadow:0 2px 10px rgba(31,35,40,.05);padding:14px 10px;
 height:auto;max-height:100%;overflow-y:auto;align-self:flex-start}
.brand{display:flex;align-items:center;gap:10px;padding:2px 8px 14px;margin-bottom:10px;border-bottom:1px solid var(--line)}
.brand img{width:34px;height:34px;border-radius:9px;flex:none}
.brand b{font-size:16px;font-weight:650;color:#1f2328;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.nav{display:flex;flex-direction:column;gap:3px}
.nav a{display:flex;align-items:center;gap:10px;padding:10px 12px;border-radius:9px;
 color:#5b6472;font-size:14px;cursor:pointer;user-select:none;white-space:nowrap}
.nav a:hover{background:#f3f6fb;color:#2b3340}
.nav a.on{background:#eaf0ff;color:var(--brand);font-weight:600}
.nav a svg{width:17px;height:17px;flex:none;stroke:currentColor;fill:none;stroke-width:1.8;
 stroke-linecap:round;stroke-linejoin:round}
/* 右侧内容区整体不滚动；卡片自己撑满高度，滚动交给卡片内部的 .card-body */
.main{flex:1;min-width:0;height:100%;overflow:hidden;padding:0}
.panel{display:none}
.panel.on{display:flex;flex-direction:column;height:100%;min-height:0}
.head{display:flex;flex-wrap:wrap;align-items:center;gap:8px 12px;min-width:0;
background:linear-gradient(120deg,#4a63d8,#6a7ce8);border-radius:14px;padding:14px 18px;
box-shadow:0 6px 18px rgba(74,99,216,.24)}
.head img{width:44px;height:44px;border-radius:11px;flex:none}
h1{font-size:20px;font-weight:650;color:#fff;margin:0;min-width:0;overflow-wrap:anywhere}
.head .badge{background:rgba(255,255,255,.22);color:#fff;font-weight:500}
/* 卡片本体固定：撑满面板高度，自身不滚动；标题栏钉在顶部，只有 .card-body 内部滚动 */
.card{position:relative;background:#fff;border:1px solid var(--line);border-radius:12px;min-width:0;
 box-shadow:0 2px 10px rgba(31,35,40,.05)}
/* 卡片高度随内容自适应（短内容收缩、长内容封顶 max-height:100% 后由内部 .card-body 滚动）；
   图片预览弹层的 .card 走自己的 #pv .card 规则，不受影响 */
.main .card{display:flex;flex-direction:column;flex:0 1 auto;height:auto;max-height:100%;min-height:0;margin:0;overflow:hidden}
/* padding-top 26px 使标题分割线与左侧品牌图标下的分割线精确对齐 */
.card h2{flex:0 0 auto;font-size:15px;font-weight:600;margin:0;display:flex;align-items:center;gap:9px;
 background:#fff;padding:26px 20px 14px 22px;border-bottom:1px solid var(--line)}
/* 卡片内容滚动区：滚动条紧贴卡片内侧右缘，滚动只发生在这里，不带动标题和卡片 */
.card-body{flex:0 1 auto;min-height:0;overflow-y:auto;overflow-x:hidden;overscroll-behavior:contain;
 padding:16px 20px 20px 22px;scrollbar-gutter:stable}
.card h2::before{content:"";width:7px;height:15px;border-radius:3px;background:var(--accent,#c9d0da);flex:none}
.c-run{--accent:var(--c-run)}.c-set{--accent:var(--c-set)}.c-api{--accent:var(--c-api)}
.c-wall{--accent:var(--c-wall)}.c-zip{--accent:var(--c-zip)}.c-help{--accent:var(--c-help)}
/* 使用说明默认收起，点击标题展开；标题固定在卡片顶部，内容在 help-body 内滚动 */
.help-summary{list-style:none;cursor:pointer;font-size:15px;font-weight:600;
display:flex;align-items:center;gap:8px;min-height:24px;
background:#fff;padding:26px 20px 14px 22px;margin:0;border-bottom:1px solid var(--line)}
.help-summary::after{content:"";width:7px;height:15px;border-radius:3px;background:var(--accent,#c9d0da);order:-1}
.help-summary::-webkit-details-marker{display:none}
.help-summary::before{content:'▸';font-size:13px;color:#656d76;flex:none;transition:transform .15s}
#helpbox[open]>.help-summary::before{transform:rotate(90deg)}
/* details 撑满卡片；标题固定，正文在 help-body 内滚动 */
#helpbox{display:flex;flex-direction:column;flex:0 1 auto;height:auto;max-height:100%;min-height:0}
.help-body{flex:0 1 auto;min-height:0;overflow-y:auto;overflow-x:hidden;overscroll-behavior:contain;
 padding:16px 20px 20px 22px;scrollbar-gutter:stable}
code{background:#f1f3f5;padding:2px 6px;border-radius:5px;font-size:12.5px;
word-break:break-all;overflow-wrap:anywhere}
a{color:#185fa5;text-decoration:none;overflow-wrap:anywhere}
/* 16px 是关键：iOS/WebView 聚焦小于 16px 的输入框会自动放大页面 */
input,select,textarea{border:1px solid #d5d9de;border-radius:6px;
padding:7px 10px;font:inherit;font-size:16px;width:100%;min-width:0;
background:#fff;color:#1f2328;-webkit-appearance:none;appearance:none}
label{display:block;font-size:13px;color:#656d76;margin-bottom:5px}
.grid{display:flex;flex-wrap:wrap;gap:12px;align-items:flex-end}
.grid>div{min-width:0;flex:1 1 210px}
.grid>div.sm{flex:0 1 170px}
.grid>div.grow{flex:1 1 260px}
.eqrow>div{flex:1 1 0;min-width:0}
.advrow{flex-wrap:nowrap}
.advrow>div.grow{flex:1 1 260px}
.advrow>div.eq{flex:1 1 0;min-width:0}
.advrow label{position:relative;cursor:help}
.advrow label .hint{display:none;position:absolute;left:0;top:100%;z-index:8;
white-space:nowrap;background:#1f2328;color:#fff;font-size:12px;font-weight:400;
padding:5px 8px;border-radius:5px;box-shadow:0 3px 10px rgba(0,0,0,.18)}
.advrow label:hover .hint{display:block}
.stats{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1fr);gap:10px 12px}
.stat{min-width:0;background:#f7f9fc;border:1px solid #eef1f5;border-radius:9px;padding:10px 12px}
.stat .k{font-size:12px;color:var(--muted);display:flex;align-items:center;gap:6px}
.stat .k::before{content:"";width:5px;height:5px;border-radius:50%;background:var(--c-run);flex:none}
.stat .v{margin-top:3px;min-width:0;overflow-wrap:anywhere;font-weight:600;font-size:13.5px}
.apis{display:flex;flex-direction:column;gap:8px}
#tasklist,#zlist{display:flex;flex-direction:column;gap:12px}
.api{display:flex;flex-wrap:wrap;align-items:center;gap:6px 10px;
padding:11px 13px;border:1px solid #eef1f5;border-radius:9px;background:#fbfcfe;
min-width:0;transition:border-color .15s,background .15s}
.api:hover{border-color:#d9e0ea;background:#f8fafd}
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
.api .tacts{flex:1 1 100%;flex-wrap:wrap}
.api .tacts button{flex:0 1 auto}
.api .note{flex:1 1 100%;font-size:12.5px;overflow-wrap:anywhere}
.cpbox{flex:1 1 100%;-webkit-user-select:text;user-select:text}
button{border:1px solid #d5d9de;background:#fff;border-radius:6px;padding:7px 12px;
cursor:pointer;font:inherit;color:#1f2328;white-space:nowrap;max-width:100%}
button.primary{background:#4a63d8;border-color:#4a63d8;color:#fff;font-weight:500}
button.primary:hover{background:#3d54c0}
button.danger{color:#b42318;border-color:#f3c3bd;background:#fff5f4}
button.danger:hover{background:#ffe9e6;border-color:#e8a49b}
button:hover{border-color:#9aa4b2}
.meta{color:#656d76;font-size:13px;margin:6px 0 0;overflow-wrap:anywhere}
.ok{color:#1a7f37}.warn{color:#b42318}
#msg{margin-top:12px;font-size:13px;min-height:18px;overflow-wrap:anywhere}
.cfgmsg{display:none;margin-top:10px;padding:9px 12px;border-radius:8px;font-size:13px;line-height:1.5;overflow-wrap:anywhere}
.cfgmsg.show{display:block}
.cfgmsg.warn{background:#fff1f0;border:1px solid #ffccc7;color:#b42318}
.cfgmsg.ok{background:#eefbf3;border:1px solid #b7ebc8;color:#1a7f37}
.kv{color:#656d76;font-size:13px;overflow-wrap:anywhere}
.badge{display:inline-block;padding:1px 7px;border-radius:10px;font-size:12px;
background:#eef1f6;color:#4a5361}
.fbar{height:8px;background:#eef1f6;border-radius:6px;overflow:hidden;margin:12px 0 8px}
.fbar>i{display:block;height:100%;width:0;background:#4a63d8;transition:width .3s}
.flog{max-height:170px;overflow:auto;background:#f6f8fa;border:1px solid #eef0f2;
border-radius:8px;padding:9px 11px;font:12px/1.65 ui-monospace,SFMono-Regular,Consolas,monospace;
color:#4a5361;white-space:pre-wrap;word-break:break-all;margin-top:10px}
.frow{display:flex;flex-wrap:wrap;align-items:center;gap:8px;margin-top:12px}
.fstatus{font-size:13px;color:#656d76;min-width:0;overflow-wrap:anywhere}
#tformbox>summary{color:var(--c-wall);font-weight:600}
#tformbox[open]>summary{margin-bottom:14px}
#tformbox{background:#fff;border:1px dashed #e6d5c4;border-radius:10px;padding:12px 14px}
#zformbox>summary{color:var(--c-zip);font-weight:600}
#zformbox[open]>summary{margin-bottom:14px}
#zformbox{background:#fff;border:1px dashed #cfe6d8;border-radius:10px;padding:12px 14px}
#zformbox .sec{color:#1c7a4d;background:#eafaf1}
.zpath input{font-size:16px}
/* Task editor: table-style sections with compact checkbox groups */
.sec{font-size:12px;font-weight:700;color:#8a5a2b;letter-spacing:.02em;
margin:16px 0 7px;padding:4px 9px;display:inline-block;
background:#fff4ea;border-radius:6px}
.sec:first-child{margin-top:0}
.filterrow{display:flex;flex-wrap:wrap;gap:0 28px}
.filterrow>div{flex:1 1 240px;min-width:0}
.opts{display:flex;flex-wrap:wrap;gap:6px 14px}
.opts label{display:inline-flex;align-items:center;gap:4px;margin:0;
font-size:14px;color:#1f2328;white-space:nowrap}
/* The global `input{appearance:none}` rule leaves native checkboxes blank in
   the fnOS WebView, so they look unselectable. Draw our own box + tick: the
   toggle itself is native, only the visual is ours, so it works everywhere. */
.opts input[type=checkbox]{-webkit-appearance:none;appearance:none;
width:17px;height:17px;flex:none;min-width:0;margin:0;padding:0;
border:1.5px solid #c2c8d0;border-radius:4px;background-color:#fff;
background-repeat:no-repeat;background-position:center;background-size:14px 14px;
cursor:pointer;vertical-align:middle}
.opts input[type=checkbox]:checked{background-color:#4a63d8;border-color:#4a63d8;
background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 16 16'%3E%3Cpath d='M3 8.5l3 3 7-7' fill='none' stroke='%23fff' stroke-width='2.5' stroke-linecap='round' stroke-linejoin='round'/%3E%3C/svg%3E")}
.opts input[type=checkbox]:disabled{opacity:.4;cursor:not-allowed}
.opts label.off{color:#a0a6ad}
/* 循环模式：开始前清空 + 执行时刻 + 周几 三项同排、同高控件 */
.sched{display:flex;flex-wrap:wrap;gap:12px 16px;align-items:flex-end}
.sched .sf{flex:1 1 0;min-width:0}
.sched .sf.week{flex:2 1 0}   /* 周几按钮多，占两份以免折行 */
.sched .sf>label{white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
/* 清空项做成与输入框同高的勾选框，保持三项视觉一致 */
.sched .clrbox{height:38px;box-sizing:border-box;align-items:center;padding:0 10px;
border:1px solid #d5d9de;border-radius:6px;background:#fff}
.sched .clrbox label{white-space:nowrap}
#day_box,#z_day_box{gap:6px}
#day_box label,#z_day_box label{position:relative;padding:0;border:0;background:none;
height:38px;min-width:38px;justify-content:center}
#day_box label span,#z_day_box label span{display:inline-flex;align-items:center;justify-content:center;
height:38px;min-width:38px;padding:0 11px;box-sizing:border-box;
border:1px solid #d5d9de;border-radius:7px;background:#fff;
font-size:14px;color:#4a5361;transition:background .15s,border-color .15s,color .15s}
#day_box label:hover span,#z_day_box label:hover span{border-color:#9aa4b2}
#day_box input:checked+span{background:#4a63d8;border-color:#4a63d8;color:#fff}
#z_day_box input:checked+span{background:var(--c-zip);border-color:var(--c-zip);color:#fff}
#day_box input[type=checkbox],#z_day_box input[type=checkbox]{position:absolute;inset:0;width:100%;height:100%;
margin:0;border:0;background:none;opacity:0;cursor:pointer;z-index:1}
.apikeybox{border:1px solid #f0e0d0;border-radius:10px;
padding:12px 14px;margin-bottom:14px;background:#fffaf5}
.apikeybox .frow{margin-top:6px}
.apikeybox input[type=password]{flex:1 1 240px}
.badge.on{background:#eefbf3;color:#1a7f37}
.badge.off{background:#fff1f0;color:#b42318}
/* select 已并入上方 input,select,textarea 规则（16px 防聚焦放大），此处保留下拉箭头 */
select{-webkit-appearance:none;appearance:none;
background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='10' height='6'%3E%3Cpath d='M1 1l4 4 4-4' stroke='%23656d76' fill='none'/%3E%3C/svg%3E");
background-repeat:no-repeat;background-position:right 10px center;padding-right:28px}
/* In-page preview: a new window is blocked by the fnOS App WebView, so show
   the image in a lightbox inside this iframe instead. */
#pv{position:fixed;top:0;left:0;right:0;bottom:0;inset:0;z-index:9999;
display:flex;align-items:center;justify-content:center;padding:14px;
background:rgba(20,24,30,.74)}
#pv .card{position:relative;background:#fff;border-radius:12px;width:100%;max-width:520px;
max-height:100%;display:flex;flex-direction:column;overflow:hidden;padding:0;
margin:0;border:1px solid #e3e6ea}
#pv .bar{display:flex;align-items:center;justify-content:space-between;gap:10px;
padding:10px 14px;border-bottom:1px solid #eef0f2;font-size:14px;min-width:0}
#pv .bar span{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
#pv .body{flex:1 1 auto;min-height:140px;display:flex;align-items:center;
justify-content:center;padding:12px;background:#f5f7fa;overflow:auto;position:relative}
#pv .frame{position:relative;display:inline-block;max-width:100%;line-height:0}
#pv img{max-width:100%;max-height:58vh;object-fit:contain;border-radius:6px;touch-action:pan-y}
#pv .pvcount{position:absolute;right:8px;bottom:8px;z-index:2;line-height:1;
padding:4px 8px;border-radius:10px;font-size:12px;font-weight:600;
background:rgba(20,24,30,.6);color:#fff;pointer-events:none;user-select:none}
#pv .err{color:#b42318;font-size:13px;overflow-wrap:anywhere;padding:8px}
#pv .foot{display:flex;flex-wrap:wrap;align-items:center;gap:8px;
padding:10px 14px;border-top:1px solid #eef0f2}
#pv .foot .u{flex:1 1 100%;font-size:12px;color:#656d76;overflow-wrap:anywhere}
/* delete confirmation with "don't remind again" */
#pv .cfm{position:absolute;inset:0;z-index:10;display:flex;align-items:center;
justify-content:center;padding:18px;background:rgba(20,24,30,.55)}
#pv .cfm .cfmcard{background:#fff;border-radius:12px;width:100%;max-width:340px;
padding:18px 18px 16px;box-shadow:0 10px 30px rgba(0,0,0,.25)}
#pv .cfm .cfmt{font-size:15px;font-weight:650;color:#1f2328;margin-bottom:8px}
#pv .cfm .cfmd{font-size:13px;line-height:1.6;color:#4a5361;overflow-wrap:anywhere}
#pv .cfm .cfmk{display:flex;align-items:center;gap:8px;margin-top:14px;font-size:14px;color:#1f2328;cursor:pointer}
#pv .cfm .cfmk input{width:16px;height:16px;min-width:0;margin:0;padding:0;
-webkit-appearance:checkbox;appearance:checkbox;accent-color:#4a63d8}
#pv .cfm .cfmact{display:flex;justify-content:flex-end;gap:8px;margin-top:16px}
@media(max-width:900px){
 .layout{flex-direction:column;align-items:stretch;height:100vh;height:100dvh;margin:0;padding:12px;gap:12px}
 .side{width:100%;flex:none;height:auto;max-height:none;overflow:visible;position:static;padding:12px}
 /* 关键：锁定主区宽度=视口减去 padding，避免被卡片内长文本 min-content 撑破屏幕 */
 .main{flex:1;min-height:0;height:auto;width:100%;min-width:0}
 .brand{padding-bottom:10px;margin-bottom:6px}
 .nav{flex-direction:row;overflow-x:auto;-webkit-overflow-scrolling:touch;gap:4px;padding-bottom:3px}
 .nav a{flex:0 0 auto;padding:9px 13px;font-size:13.5px}
}
@media(max-width:640px){
 .wrap{margin:16px auto 40px;padding:0 12px}
 .card-body,.help-body{padding:12px 14px 16px}
 h1{font-size:19px}
 .grid>div,.grid>div.sm,.grid>div.grow{flex:1 1 100%}
 .sched .sf,.sched .sf.week{flex:1 1 100%}
 .advrow{flex-wrap:wrap}
 .advrow>div.grow{flex:1 1 100%}
 .advrow>div.eq{flex:1 1 45%}
 .stats{gap:10px 12px}
 .api{gap:6px 8px;max-width:100%}
 .api .name{max-width:100%;min-width:0}
 .api .name .badge{max-width:100%;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;vertical-align:bottom}
 .api .note{max-width:100%;min-width:0}
 .api .acts{max-width:100%}
 .frow>*{max-width:100%}
 .frow input{flex:1 1 140px;width:auto;min-width:0}
 .api .acts{gap:6px}
 .api .acts button{padding:6px 9px;font-size:13px}
 .api .acts a{font-size:13px}
}
</style></head><body><div class="layout">
<aside class="side">
<div class="brand"><img src="$base/_icon" alt=""><b>$title</b></div>
<nav class="nav" id="nav">
<a data-p="run" class="on" title="概览"><svg viewBox="0 0 24 24"><rect x="3" y="3" width="7" height="7" rx="1.5"/><rect x="14" y="3" width="7" height="7" rx="1.5"/><rect x="3" y="14" width="7" height="7" rx="1.5"/><rect x="14" y="14" width="7" height="7" rx="1.5"/></svg>概览</a>
<a data-p="api" title="接口列表"><svg viewBox="0 0 24 24"><path d="M4 6h16M4 12h16M4 18h16"/><circle cx="7" cy="6" r="1.4" fill="currentColor" stroke="none"/><circle cx="7" cy="12" r="1.4" fill="currentColor" stroke="none"/><circle cx="7" cy="18" r="1.4" fill="currentColor" stroke="none"/></svg>接口列表</a>
<a data-p="wall" title="壁纸采集"><svg viewBox="0 0 24 24"><rect x="3" y="4" width="18" height="16" rx="2"/><circle cx="8.5" cy="9.5" r="1.6"/><path d="M4 17l5-5 4 3 3-3 4 4"/></svg>壁纸采集</a>
<a data-p="zip" title="图片压缩"><svg viewBox="0 0 24 24"><path d="m12 3 9 5-9 5-9-5 9-5Z"/><path d="m3 13 9 5 9-5"/><path d="m3 17 9 5 9-5"/></svg>图片压缩</a>
<a data-p="set" title="设置"><svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="3.2"/><path d="M19.4 15a1.7 1.7 0 0 0 .34 1.88l.06.06a2 2 0 1 1-2.83 2.83l-.06-.06a1.7 1.7 0 0 0-1.88-.34 1.7 1.7 0 0 0-1.03 1.56V21a2 2 0 1 1-4 0v-.09A1.7 1.7 0 0 0 8.94 19.3a1.7 1.7 0 0 0-1.88.34l-.06.06a2 2 0 1 1-2.83-2.83l.06-.06A1.7 1.7 0 0 0 4.57 15a1.7 1.7 0 0 0-1.56-1.03H3a2 2 0 1 1 0-4h.09A1.7 1.7 0 0 0 4.7 8.94a1.7 1.7 0 0 0-.34-1.88l-.06-.06a2 2 0 1 1 2.83-2.83l.06.06A1.7 1.7 0 0 0 9 4.57a1.7 1.7 0 0 0 1.03-1.56V3a2 2 0 1 1 4 0v.09A1.7 1.7 0 0 0 15.06 4.7a1.7 1.7 0 0 0 1.88-.34l.06-.06a2 2 0 1 1 2.83 2.83l-.06.06A1.7 1.7 0 0 0 19.43 9v.09A1.7 1.7 0 0 0 21 10.12h.09a2 2 0 1 1 0 4H21a1.7 1.7 0 0 0-1.56 1.03z"/></svg>设置</a>
<a data-p="help" title="使用说明"><svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="9"/><path d="M9.6 9.2a2.5 2.5 0 1 1 3.9 2.1c-.9.6-1.5 1.1-1.5 2.2"/><path d="M12 17.2h.01" stroke-width="2.4"/></svg>使用说明</a>
</nav>
</aside>
<main class="main">
<section class="panel on" id="panel-run">
<div class="card c-run"><h2>运行状态</h2><div class="card-body"><div class="stats">
<div class="stat"><div class="k">图片根目录</div><div class="v"><code>$root</code></div></div>
<div class="stat"><div class="k">接口 / 图片</div><div class="v">$apicount 个接口 · $imgcount 张图片
<span class="kv">（扫描缓存 $ttl 秒）</span></div></div>
<div class="stat"><div class="k">网关入口</div><div class="v $gwclass">$gwstate</div></div>
<div class="stat"><div class="k">目录状态</div><div class="v $stateclass">$state</div></div>
<div class="stat"><div class="k">壁纸采集任务</div><div class="v" id="ovFetch">—</div></div>
<div class="stat"><div class="k">图片压缩任务</div><div class="v" id="ovZip">—</div></div>
<div class="stat"><div class="k">版本号</div><div class="v">v$version</div></div>
</div></div></div>
</section>

<section class="panel" id="panel-api">
<div class="card c-api"><h2>接口列表</h2><div class="card-body"><div class="apis">$rows</div></div></div>
</section>

<section class="panel" id="panel-set">
<div class="card c-set"><h2>设置</h2><div class="card-body">
<div class="grid">
<div class="sm"><label for="f_port">服务端口</label><input id="f_port" type="number" min="1024" max="65535" value="$port"></div>
<div class="grow"><label for="f_root">图片根目录（留空=自动使用已授权目录）</label>
<input id="f_root" type="text" value="$root_value" placeholder="留空即自动跟随应用权限中授权的文件夹"></div>
<div class="sm"><label for="f_ttl">缓存秒数</label><input id="f_ttl" type="number" min="1" max="3600" value="$ttl"></div>
</div>
<div style="margin-top:14px"><button class="primary" id="save">保存并应用</button>
<button id="reload" style="margin-left:8px">立即刷新</button></div>
<div id="cfgmsg" class="cfgmsg"></div>
<div id="msg"></div></div></div>
</section>

<section class="panel" id="panel-wall">
<div class="card c-wall"><h2>Wallhaven壁纸采集</h2><div class="card-body">
<div class="apikeybox">
<label for="api_key">API Key（留空则仅下载 SFW）</label>
<div class="frow"><input id="api_key" type="password" placeholder="留空并保存=清除 Key，仅下载 SFW">
<button class="primary" id="keysave">保存 API Key</button>
<span class="badge" id="keystate">检测中…</span></div>
</div>
<div id="tasklist"></div>
<div class="frow"><button class="primary" id="tnew">+ 新建任务</button></div>
<details id="tformbox" style="margin-top:14px"><summary style="cursor:pointer;font-size:13px;color:#656d76">任务参数与筛选条件</summary>
<div class="grid eqrow">
<div><label for="t_name">任务名称</label><input id="t_name" type="text" placeholder="例如 每日动漫壁纸"></div>
<div><label for="t_target">目标分类（子文件夹名）</label><input id="t_target" type="text" value="Wallhaven"></div>
<div><label for="t_count">每次下载张数</label><input id="t_count" type="number" min="1" max="200" value="24"></div>
<div><label for="t_enabled">状态</label><select id="t_enabled"><option value="1">启用</option><option value="0">停用</option></select></div>
</div>
<div class="sec">循环模式</div>
<div class="sched">
<div class="sf clr"><label>开始前清空目标分类文件夹</label>
<div class="opts clrbox"><label><input type="checkbox" id="t_clear"><span>清空后再采集</span></label></div></div>
<div class="sf tm"><label for="t_time">执行时刻（HH:MM）</label><input id="t_time" type="text" value="03:00" placeholder="03:00"></div>
<div class="sf week">
<label>每周（全不选=单次）</label>
<div class="opts" id="day_box">
<label><input type="checkbox" id="day1" value="1"><span>一</span></label>
<label><input type="checkbox" id="day2" value="2"><span>二</span></label>
<label><input type="checkbox" id="day3" value="3"><span>三</span></label>
<label><input type="checkbox" id="day4" value="4"><span>四</span></label>
<label><input type="checkbox" id="day5" value="5"><span>五</span></label>
<label><input type="checkbox" id="day6" value="6"><span>六</span></label>
<label><input type="checkbox" id="day7" value="7"><span>日</span></label>
</div>
</div>
</div>
<div class="filterrow" style="margin-top:14px">
<div>
<div class="sec">壁纸类型</div>
<div class="opts" id="cat_box">
<label><input type="checkbox" id="cat0">通用</label>
<label><input type="checkbox" id="cat1">动漫</label>
<label><input type="checkbox" id="cat2">人物</label>
</div>
</div>
<div>
<div class="sec">纯净度</div>
<div class="opts" id="pur_box">
<label><input type="checkbox" id="pur0">SFW</label>
<label id="pur1_l"><input type="checkbox" id="pur1">Sketchy</label>
<label id="pur2_l"><input type="checkbox" id="pur2">NSFW</label>
</div>
</div>
</div>
<div class="filterrow" style="margin-top:14px">
<div>
<div class="sec">比例（全不选=不限）</div>
<div class="opts" id="ratio_box">
<label><input type="checkbox" value="landscape">横屏</label>
<label><input type="checkbox" value="portrait">竖屏</label>
<label><input type="checkbox" value="1x1">正方形</label>
</div>
</div>
<div>
<div class="sec">排序（单选）</div>
<div class="opts" id="sort_box">
<label><input type="checkbox" value="hot">热门</label>
<label><input type="checkbox" value="toplist">最近一周</label>
<label><input type="checkbox" value="favorites">收藏量</label>
<label><input type="checkbox" value="views">浏览量</label>
</div>
</div>
</div>
<div class="sec">高级筛选</div>
<div class="grid advrow">
<div class="eq"><label for="t_start">起始页码<span class="hint">0=随机</span></label><input id="t_start" type="number" min="0" max="500" value="0"></div>
<div class="eq"><label for="t_end">结束页码<span class="hint">0=不限</span></label><input id="t_end" type="number" min="0" max="500" value="0"></div>
<div class="eq"><label for="t_short">尺寸限制<span class="hint">短边≥px，0=不限</span></label><input id="t_short" type="number" min="0" max="10000" value="0"></div>
<div class="eq"><label for="t_minfav">最小收藏数<span class="hint">0=不限</span></label><input id="t_minfav" type="number" min="0" value="0"></div>
<div class="eq"><label for="t_minsize">最小体积 KB<span class="hint">0=不限</span></label><input id="t_minsize" type="number" min="0" value="0"></div>
<div class="eq"><label for="t_maxsize">最大体积 MB<span class="hint">0=不限</span></label><input id="t_maxsize" type="number" min="0" value="0"></div>
</div>
<div class="frow"><button class="primary" id="tsave">保存任务</button><button id="tcancel">取消</button></div>
<p class="meta" id="tformmsg"></p>
</details>
<div class="cfgmsg" id="tmsg"></div>
<div class="flog" id="tlog" style="display:none"></div>
</div></div>
</section>

<section class="panel" id="panel-zip">
<div class="card c-zip"><h2>图片压缩</h2><div class="card-body">
<p class="meta">把目录里的图片转为 JPG、限制高度与体积，原图自动备份。使用系统自带的 ffmpeg。</p>
<div id="zlist"></div>
<div class="frow"><button class="primary" id="znew">+ 新建压缩任务</button></div>
<details id="zformbox" style="margin-top:14px"><summary style="cursor:pointer;font-size:13px;color:#656d76">压缩任务参数</summary>
<div class="grid eqrow">
<div><label for="z_name">任务名称</label><input id="z_name" type="text" placeholder="例如 每日压缩壁纸"></div>
<div class="zpath"><label for="z_src">源目录</label><input id="z_src" type="text" value="/vol2/1000/Media/Wallhaven" placeholder="绝对路径"></div>
<div class="zpath"><label for="z_backup">备份目录</label><input id="z_backup" type="text" value="/vol2/1000/Media/Image/Wall-Backup" placeholder="绝对路径"></div>
<div><label for="z_enabled">状态</label><select id="z_enabled"><option value="1">启用</option><option value="0">停用</option></select></div>
</div>
<div class="sec">压缩规则</div>
<div class="grid advrow">
<div class="eq"><label for="z_height">短边最大PX<span class="hint">0=不限，宽高较小一边</span></label><input id="z_height" type="number" min="0" max="20000" value="2160"></div>
<div class="eq"><label for="z_size">最大体积 MB<span class="hint">0=不限</span></label><input id="z_size" type="number" min="0" max="2000" value="5"></div>
<div class="eq"><label for="z_qmax">质量上限<span class="hint">98=高保真</span></label><input id="z_qmax" type="number" min="1" max="100" value="98"></div>
<div class="eq"><label for="z_qmin">质量下限<span class="hint">底线</span></label><input id="z_qmin" type="number" min="1" max="100" value="85"></div>
</div>
<div class="opts" style="margin-top:12px">
<label><input type="checkbox" id="z_tojpg" checked>非 JPG 转 JPG</label>
<label><input type="checkbox" id="z_rec">包含子目录</label>
</div>
<div class="sec">循环模式</div>
<div class="sched">
<div class="sf tm"><label for="z_time">执行时刻（HH:MM）</label><input id="z_time" type="text" value="03:00" placeholder="03:00"></div>
<div class="sf week">
<label>每周（全不选=单次）</label>
<div class="opts" id="z_day_box">
<label><input type="checkbox" id="zday1" value="1"><span>一</span></label>
<label><input type="checkbox" id="zday2" value="2"><span>二</span></label>
<label><input type="checkbox" id="zday3" value="3"><span>三</span></label>
<label><input type="checkbox" id="zday4" value="4"><span>四</span></label>
<label><input type="checkbox" id="zday5" value="5"><span>五</span></label>
<label><input type="checkbox" id="zday6" value="6"><span>六</span></label>
<label><input type="checkbox" id="zday7" value="7"><span>日</span></label>
</div>
</div>
</div>
<div class="frow"><button class="primary" id="zsave">保存任务</button><button id="zcancel">取消</button></div>
<p class="meta" id="zformmsg"></p>
</details>
<div class="cfgmsg" id="zmsg"></div>
<div class="flog" id="zlog" style="display:none"></div>
</div></div>
</section>

<section class="panel" id="panel-help">
<div class="card c-help"><details id="helpbox" open><summary class="help-summary">使用说明</summary><div class="help-body">
<p class="meta"><b>新增接口</b>：图库里新建子文件夹并放入图片，最多等 $ttl 秒自动生效；结构为 <code>分类名/*.jpg</code>，接口名不区分大小写。</p>
<p class="meta"><b>缓存</b>：只缓存目录扫描结果 $ttl 秒，不缓存图片；改图后点「立即刷新」即时生效。</p>
<p class="meta"><b>复制地址</b>：给出随机接口，跟随当前域名/IP，端口固定为 $port，可直接外链；网关地址 <code>$gwurl</code> 仅登录态可用。</p>
<p class="meta"><b>打开看看</b>：按下载时间由近到远看图、可滑动切换；「删除」会拉黑该图，「魔术师」批量补拉黑。</p>
<p class="meta"><b>采集任务</b>：周几全不选=单次、勾选=每周定时；按接口顺序下载、只取原图，已下载 ID 记入 <code>downloaded.txt</code>；无 API Key 时强制仅 SFW。</p>
<p class="meta"><b>压缩任务</b>：源目录图片转 JPG，短边超限则缩小、体积超限则降质，原图备份一次；用系统 ffmpeg。源目录与备份目录需在应用权限中授权。</p>
<p class="meta">接口 <a href="$base/_apis">/_apis</a> · 健康检查 <a href="$base/_health">/_health</a></p>
</div></details></div>
</section>
</main></div>
<script>
var BASE='$base', GATEWAY=$gateway, DIRECT='$direct', PORT=$port;
var TDEF=$tdef, CDEF=$cdef;
/* two-column nav: switch panels, remember last tab */
function switchTab(p){
  var navs=document.querySelectorAll('#nav a'),ps=document.querySelectorAll('.panel');
  for(var i=0;i<navs.length;i++)navs[i].classList.toggle('on',navs[i].getAttribute('data-p')===p);
  for(var j=0;j<ps.length;j++)ps[j].classList.toggle('on',ps[j].id==='panel-'+p);
  try{localStorage.setItem('ranpix_tab',p)}catch(e){}
  /* 卡片内滚动方案：切回面板时把它的内容滚动区复位到顶部 */
  var active=document.querySelector('.panel.on');
  if(active){var b=active.querySelector('.card-body,.help-body');if(b)b.scrollTop=0;}
}
(function(){
  var navs=document.querySelectorAll('#nav a');
  for(var i=0;i<navs.length;i++)(function(a){
    a.onclick=function(){switchTab(a.getAttribute('data-p'));};
  })(navs[i]);
  var last='run';try{last=localStorage.getItem('ranpix_tab')||'run'}catch(e){}
  if(!document.getElementById('panel-'+last))last='run';
  switchTab(last);
})();
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
var pvEl=null,pvP='',pvStage=0,pvSeq=0,pvIdx=0,pvTotal=0;
var PV_NOREMIND='ranpix_del_noremind';
function pvClose(){if(pvEl&&pvEl.parentNode){pvEl.parentNode.removeChild(pvEl)}pvEl=null;}
function pvResetDel(){var b=document.getElementById('pvDel');if(b){b.disabled=false;b.textContent='删除';}}
function pvLoad(){
  pvResetDel();
  var img=document.getElementById('pvImg'),err=document.getElementById('pvErr');
  pvStage=0;err.style.display='none';img.style.display='';
  pvSeq++;
  /* 预览按下载时间由近到远顺序浏览；复制链接始终是不带参数的随机接口 */
  var q='order=recent&i='+pvIdx+'&_='+Date.now()+'-'+pvSeq;
  img.src=gwUrl(pvP)+'?'+q;
  var n=document.getElementById('pvIdx');
  if(n){var shown=pvTotal?(pvIdx%pvTotal)+1:pvIdx+1;n.textContent=shown+'/'+(pvTotal||'?');}
}
function pvFail(){
  var img=document.getElementById('pvImg'),err=document.getElementById('pvErr');
  if(pvStage===0){pvStage=1;img.src=directUrl(pvP)+'?order=recent&i='+pvIdx+'&_='+Date.now()+'-'+pvSeq;return;}
  img.style.display='none';err.style.display='block';
  err.textContent='图片加载失败。请在与 NAS 同一网络的浏览器中打开这个直连地址：'+directUrl(pvP);
}
function pvPrev(){pvIdx=Math.max(0,pvIdx-1);pvLoad();}
function pvNext(){pvIdx++;pvLoad();}
/* 自定义确认框：支持「不再提醒」勾选，避免 WebView 原生 confirm 无法带选项 */
function pvAsk(title,desc,showCheck,okText,onYes){
  var box=document.getElementById('pvCfm');if(!box)return;
  document.getElementById('pvCfmt').textContent=title;
  document.getElementById('pvCfmd').textContent=desc;
  document.getElementById('pvCfmk').style.display=showCheck?'flex':'none';
  document.getElementById('pvCfmYes').textContent=okText||'确定';
  document.getElementById('pvCfmNo').textContent=showCheck?'取消':'关闭';
  if(showCheck)document.getElementById('pvNoRemind').checked=false;
  box.style.display='flex';
  document.getElementById('pvCfmNo').onclick=function(){box.style.display='none';};
  document.getElementById('pvCfmYes').onclick=function(){
    if(showCheck&&document.getElementById('pvNoRemind').checked){
      try{localStorage.setItem(PV_NOREMIND,'1')}catch(e){}
    }
    box.style.display='none';
    if(onYes)onYes();
  };
}
function pvShow(p,n){
  pvP=p;pvIdx=0;pvTotal=n||0;
  if(!pvEl){
    pvEl=document.createElement('div');pvEl.id='pv';
    pvEl.innerHTML='<div class="card"><div class="bar"><span id="pvTitle"></span>'+
      '<button id="pvX" type="button">关闭</button></div>'+
      '<div class="body"><div class="frame"><img id="pvImg" alt="">'+
      '<span id="pvIdx" class="pvcount"></span></div>'+
      '<div id="pvErr" class="err" style="display:none"></div></div>'+
      '<div class="foot"><button id="pvPrev" type="button">上一张</button>'+
      '<button id="pvNext" type="button">下一张</button>'+
      '<button id="pvMagic" type="button">魔术师</button>'+
      '<button id="pvDel" class="danger" type="button">删除</button></div>'+
      '<div id="pvCfm" class="cfm" style="display:none"><div class="cfmcard">'+
      '<div class="cfmt" id="pvCfmt"></div><div class="cfmd" id="pvCfmd"></div>'+
      '<label class="cfmk" id="pvCfmk"><input type="checkbox" id="pvNoRemind">不再提醒</label>'+
      '<div class="cfmact"><button id="pvCfmNo" type="button">取消</button>'+
      '<button id="pvCfmYes" class="danger" type="button">删除</button></div></div></div></div>';
    document.body.appendChild(pvEl);
    pvEl.addEventListener('click',function(e){if(e.target===pvEl)pvClose()});
    document.getElementById('pvX').onclick=pvClose;
    document.getElementById('pvPrev').onclick=pvPrev;
    document.getElementById('pvNext').onclick=pvNext;
    document.getElementById('pvDel').onclick=function(){pvDelete()};
    document.getElementById('pvMagic').onclick=function(){pvMagic()};
    document.getElementById('pvImg').onerror=function(){pvFail()};
    /* 手机端手势：左滑下一张、右滑上一张（只认明显水平位移，避免与纵向滚动冲突） */
    var bEl=pvEl.querySelector('.body'),tsX=0,tsY=0;
    bEl.addEventListener('touchstart',function(e){
      if(e.touches.length===1){tsX=e.touches[0].clientX;tsY=e.touches[0].clientY;}
    },{passive:true});
    bEl.addEventListener('touchend',function(e){
      if(!e.changedTouches||e.changedTouches.length!==1)return;
      var dx=e.changedTouches[0].clientX-tsX,dy=e.changedTouches[0].clientY-tsY;
      if(Math.abs(dx)<45||Math.abs(dx)<Math.abs(dy)*1.4)return;
      if(dx<0)pvNext();else pvPrev();
    },{passive:true});
  }
  document.getElementById('pvTitle').textContent='/'+decodeURIComponent(p)+' · 按下载时间浏览';
  pvLoad();
}
function pvDelete(){
  var btn=document.getElementById('pvDel');if(!btn||btn.disabled)return;
  var go=function(){
    btn.disabled=true;
    fetch(BASE+'/_image/delete',{method:'POST',
      headers:{'Content-Type':'application/x-www-form-urlencoded'},
      body:'cat='+encodeURIComponent(pvP)+'&i='+pvIdx})
     .then(function(r){return r.json()}).then(function(j){
       if(!j.ok){btn.disabled=false;btn.textContent='删除失败';msg('删除失败：'+(j.error||'未知错误'),'warn');return;}
       /* 删除成功后不展示任何"已删除/已拉黑"状态：图片已删，按钮状态纯属多余。
          直接切到下一张，pvLoad() 会把按钮恢复为"删除"，全程无多余中间态。 */
       if(pvTotal>0)pvTotal--;
       pvLoad();
     }).catch(function(e){btn.disabled=false;btn.textContent='删除失败';msg('请求失败：'+e,'warn')});
  };
  var silent=false;try{silent=localStorage.getItem(PV_NOREMIND)==='1'}catch(e){}
  if(silent){go();return;}
  pvAsk('删除这张图片？','删除后会加入全局黑名单，以后任何采集任务扫到它都会自动跳过。',true,'删除',go);
}
/* 魔术师：把「downloaded.txt 有记录但文件已被外部删除」的图片批量拉黑 */
function pvMagic(){
  var btn=document.getElementById('pvMagic');if(!btn||btn.disabled)return;
  pvAsk('魔术师 · 批量拉黑',
    '扫描所有分类，把「已下载过、但图片文件已不在」的条目批量加入全局黑名单。适合你用文件管理器删除图片后使用。',
    false,'开始扫描',function(){
      var old=btn.textContent;btn.disabled=true;btn.textContent='扫描中…';
      fetch(BASE+'/_image/magician',{method:'POST'})
       .then(function(r){return r.json()}).then(function(j){
         btn.disabled=false;btn.textContent=old;
         if(!j.ok){pvAsk('扫描失败',j.error||'未知错误',false,'知道了',null);return;}
         pvAsk('魔术师完成',
           '已扫描 '+j.scanned+' 条下载记录，发现 '+j.missing+' 张已删除的图片，新拉黑 '+j.added+' 个 ID（黑名单现共 '+j.total+' 个）。',
           false,'知道了',null);
       }).catch(function(e){btn.disabled=false;btn.textContent=old;pvAsk('扫描失败',String(e),false,'知道了',null)});
    });
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
        if(b.tagName==='A'&&cls.indexOf(' pv ')>=0){e.preventDefault();pvShow(p,parseInt(b.getAttribute('data-n'),10)||0);return;}
        if(b.tagName==='BUTTON'&&cls.indexOf(' cp ')>=0){copyUrl(b);return;}
      }
    }
    b=b.parentNode;
  }
});
function cfgMsg(t,c){var e=document.getElementById('cfgmsg');if(!e)return;e.textContent=t;e.className='cfgmsg show '+(c||'');}
document.getElementById('save').onclick=function(){
  var btn=this;btn.disabled=true;cfgMsg('正在保存…','');msg('正在保存…');
  var enc=encodeURIComponent;
  var body='port='+enc(document.getElementById('f_port').value)
    +'&image_root='+enc(document.getElementById('f_root').value)
    +'&cache_ttl='+enc(document.getElementById('f_ttl').value);
  fetch(BASE+'/_config',{method:'POST',headers:{'Content-Type':'application/x-www-form-urlencoded'},body:body})
   .then(function(r){return r.json()}).then(function(j){
     btn.disabled=false;
     if(!j.ok){var t='保存失败：'+(j.error||'未知错误')+'（本次未保存任何设置）';cfgMsg(t,'warn');msg(t,'warn');return;}
     cfgMsg('已保存并生效：图库 '+j.image_root+' · 缓存 '+j.cache_ttl+' 秒','ok');
     if(j.restart){
       msg('端口已改为 '+j.port+'，正在重启服务…','ok');
       if(GATEWAY){setTimeout(function(){location.reload()},1800);}
       else{var u=location.protocol+'//'+location.hostname+':'+j.port+'/';
            setTimeout(function(){location.href=u},1600);}
     }else{
       msg('已保存，'+(j.message||'配置已生效'),'ok');
       setTimeout(function(){location.reload()},900);
     }
   }).catch(function(e){btn.disabled=false;var t='请求失败：'+e;cfgMsg(t,'warn');msg(t,'warn')});
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
/* ---- Wallhaven collector (stage 1) ---- */
function esc(x){return String(x==null?'':x).replace(/&/g,'&amp;').replace(/</g,'&lt;')
  .replace(/>/g,'&gt;').replace(/"/g,'&quot;');}
function tpost(path,extra,cb){
  var p=[];
  for(var k in extra||{}){if(Object.prototype.hasOwnProperty.call(extra,k))p.push(encodeURIComponent(k)+'='+encodeURIComponent(extra[k]));}
  fetch(BASE+path,{method:'POST',headers:{'Content-Type':'application/x-www-form-urlencoded'},body:p.join('&')})
   .then(function(r){return r.json()}).then(cb)
   .catch(function(e){tmsg('请求失败：'+e,'warn')});
}
function tmsg(text,kind){
  var el=document.getElementById('tmsg');el.textContent=text;
  el.className='cfgmsg show'+(kind?' '+kind:'');
}
function clearMsg(){document.getElementById('tmsg').className='cfgmsg';}
function val(id){var e=document.getElementById(id);return e?String(e.value||'').trim():'';}
function maskFrom(p,n){var s='';for(var i=0;i<n;i++)s+=document.getElementById(p+i).checked?'1':'0';return s;}
function setMask(p,s){s=s||'';for(var i=0;i<3;i++){var el=document.getElementById(p+i);if(el)el.checked=s.charAt(i)==='1';}}
function daysFrom(){var s='';for(var d=1;d<=7;d++)if(document.getElementById('day'+d).checked)s+=String(d);return s;}
function setDays(s){s=s||'';for(var d=1;d<=7;d++)document.getElementById('day'+d).checked=s.indexOf(String(d))>=0;}
function ratiosFrom(){var a=[],els=document.querySelectorAll('#ratio_box input:checked');
  for(var i=0;i<els.length;i++)a.push(els[i].value);return a.join(',');}
function setRatios(s){var a=String(s||'').split(','),els=document.querySelectorAll('#ratio_box input');
  for(var i=0;i<els.length;i++)els[i].checked=a.indexOf(els[i].value)>=0;}
function sortFrom(){var els=document.querySelectorAll('#sort_box input');
  for(var i=0;i<els.length;i++)if(els[i].checked)return els[i].value;return 'hot';}
function setSort(s){s=s||'hot';var els=document.querySelectorAll('#sort_box input');
  for(var i=0;i<els.length;i++)els[i].checked=els[i].value===s;}
(function(){var box=document.getElementById('sort_box');if(!box)return;
  box.addEventListener('change',function(e){
    var t=e.target;if(!t||t.tagName!=='INPUT')return;
    if(!t.checked){t.checked=true;return;}   /* single-choice: keep one selected */
    var els=box.querySelectorAll('input');
    for(var i=0;i<els.length;i++)if(els[i]!==t)els[i].checked=false;
  });
})();
var apiKeySet=false;
function applyKeyState(set){
  apiKeySet=!!set;
  var el=document.getElementById('keystate');
  el.textContent=apiKeySet?'已设置 · 可选 Sketchy / NSFW':'未设置 · 仅 SFW';
  el.className='badge '+(apiKeySet?'on':'off');
  var ids=['pur1','pur2'];
  for(var i=0;i<ids.length;i++){
    var x=document.getElementById(ids[i]);if(!x)continue;
    x.disabled=!apiKeySet;
    var l=document.getElementById(ids[i]+'_l');if(l)l.className=apiKeySet?'':'off';
  }
  if(!apiKeySet){for(i=0;i<ids.length;i++)document.getElementById(ids[i]).checked=false;}
}
document.getElementById('keysave').onclick=function(){
  var btn=this;btn.disabled=true;
  tpost('/_api_key',{api_key:document.getElementById('api_key').value},function(j){
    btn.disabled=false;
    if(j.ok){tmsg(j.message,'ok');applyKeyState(j.api_key_set);poll();}
    else tmsg(j.error||'保存失败','warn');
  });
};
function tcfgFromForm(){
  return {type:'fetch',target:val('t_target'),count:val('t_count'),
    categories:maskFrom('cat',3),purity:maskFrom('pur',3),
    ratios:ratiosFrom(),sorting:sortFrom(),
    short_edge:val('t_short'),start_page:val('t_start'),end_page:val('t_end'),
    min_favorites:val('t_minfav'),min_size_kb:val('t_minsize'),
    max_size_mb:val('t_maxsize'),query:'',api_key:'',
    clear_before:document.getElementById('t_clear').checked?'1':'0'};
}
function fillForm(cfg){
  setMask('cat',cfg.categories||'111');
  setMask('pur',cfg.purity||'100');
  setRatios(cfg.ratios||'');
  setSort(cfg.sorting||'hot');
  var map={t_target:'target',t_count:'count',t_short:'short_edge',
    t_start:'start_page',t_end:'end_page',t_minfav:'min_favorites',
    t_minsize:'min_size_kb',t_maxsize:'max_size_mb'};
  for(var id in map){if(Object.prototype.hasOwnProperty.call(map,id)){
    var el=document.getElementById(id);if(el)el.value=cfg[map[id]]==null?'':cfg[map[id]];}}
  document.getElementById('t_clear').checked=!!cfg.clear_before;
  applyKeyState(apiKeySet);
}
function resetForm(){
  document.getElementById('t_name').value='';
  document.getElementById('t_time').value='03:00';
  document.getElementById('t_enabled').value='1';
  setDays('1234567');
  fillForm(TDEF);
  editingId='';
}
var editingId='';
var TSTATUS={'idle':'就绪','running':'采集中','done':'已完成','error':'失败',
  'cancelled':'已停止','empty':'无匹配图'};
var DAYN={'1':'一','2':'二','3':'三','4':'四','5':'五','6':'六','7':'日'};
var SORTN={hot:'热门',toplist:'最近一周',favorites:'收藏量',views:'浏览量'};
var RATIOMAP={landscape:'横屏',portrait:'竖屏','1x1':'正方形',
  '16x9':'16:9','16x10':'16:10','3x2':'3:2','4x3':'4:3','5x4':'5:4',
  '21x9':'21:9','32x9':'32:9','48x9':'48:9',
  '9x16':'9:16','10x16':'10:16','9x18':'9:18'};
function ratioLabel(s){
  if(!s)return '';
  var a=String(s).split(','),out=[];
  for(var i=0;i<a.length;i++)out.push(RATIOMAP[a[i]]||a[i]);
  return out.join('/');
}
function dayLabel(s){
  s=s||'';if(!s)return '单次';
  var a=[];for(var i=0;i<s.length;i++)a.push('周'+(DAYN[s.charAt(i)]||s.charAt(i)));
  return '每周'+a.join('/');
}
function filterLabel(cfg){
  cfg=cfg||{};var r=[];
  if(cfg.categories&&cfg.categories!=='111')r.push('类型'+cfg.categories);
  if(cfg.purity&&cfg.purity!=='100')r.push('纯度'+cfg.purity);
  if(cfg.ratios)r.push('比例'+ratioLabel(cfg.ratios));
  r.push('第'+(cfg.start_page?cfg.start_page:'随机')+'页-'+(cfg.end_page?cfg.end_page:'不限'));
  r.push((SORTN[cfg.sorting]||cfg.sorting||'Hot')+'排序');
  return r.join(' · ');
}
function renderTasks(tasks,now){
  var box=document.getElementById('tasklist');
  tasks=tasks.filter(function(t){return (t.type||'fetch')!=='compress';});
  if(!tasks.length){box.innerHTML='<p class="meta">还没有采集任务，点下方「新建任务」开始。</p>';return;}
  var h='';
  for(var i=0;i<tasks.length;i++){
    var t=tasks[i];
    var st=t.running?'运行中':(TSTATUS[t.phase]||TSTATUS[t.last_status]||t.last_status||'就绪');
    var prog=t.running&&t.total>0?(' '+t.done+'/'+t.total+' 张'):'';
    var last=t.last_run?('上次 '+esc(t.last_run)+' · '+esc(t.last_count)+' 张'):'尚未运行';
    var due=(!t.running&&t.enabled&&t.time===now)?' · 本分钟待触发':'';
    h+='<div class="api"><div class="name"><b>'+esc(t.name)+'</b> '
      +'<span class="badge">'+esc(t.target)+'</span> '
      +'<span class="badge">'+esc(t.time)+' · '+esc(dayLabel(t.days))+'</span></div>';
    h+='<div class="note">'+esc(st)+esc(prog)+' · '+(t.enabled?'已启用':'已停用')
      +' · 每次 '+esc(t.count)+' 张 · '+esc(filterLabel(t.cfg))+'</div>';
    h+='<div class="note">'+esc(last)+esc(due)+'</div>';
    if(t.error)h+='<div class="note warn">'+esc(t.error)+'</div>';
    h+='<div class="acts tacts">';
    h+='<button data-act="toggle" data-id="'+esc(t.id)+'">'+(t.enabled?'停用':'启用')+'</button>';
    h+='<button data-act="run" data-id="'+esc(t.id)+'"'+(t.running?' disabled':'')+'>立即运行</button>';
    h+='<button data-act="stop" data-id="'+esc(t.id)+'"'+(t.running?'':' disabled')+'>停止</button>';
    h+='<button data-act="edit" data-id="'+esc(t.id)+'">编辑</button>';
    h+='<button data-act="log" data-id="'+esc(t.id)+'">日志</button>';
    h+='<button data-act="delete" data-id="'+esc(t.id)+'">删除</button>';
    h+='</div></div>';
  }
  box.innerHTML=h;
}
/* ---- image compression tasks (share the same task queue & scheduler) ---- */
var ZSTATUS={'idle':'就绪','running':'压缩中','done':'已完成','error':'失败',
  'cancelled':'已停止','empty':'无需要处理'};
function zcfgLabel(cfg){
  cfg=cfg||{};var r=[];
  r.push('短边≤'+(cfg.max_height?cfg.max_height:'不限'));
  r.push('体积≤'+(cfg.max_size_mb?cfg.max_size_mb+'MB':'不限'));
  r.push('质量'+(cfg.q_min||85)+'-'+(cfg.q_max||98));
  r.push(cfg.to_jpg?'转JPG':'仅压JPG');
  if(cfg.recursive)r.push('含子目录');
  return r.join(' · ');
}
function renderZipTasks(tasks,now){
  var box=document.getElementById('zlist');
  tasks=tasks.filter(function(t){return t.type==='compress';});
  if(!tasks.length){box.innerHTML='<p class="meta">还没有压缩任务，点下方「新建压缩任务」开始。</p>';return;}
  var h='';
  for(var i=0;i<tasks.length;i++){
    var t=tasks[i];
    var st=t.running?'运行中':(ZSTATUS[t.phase]||ZSTATUS[t.last_status]||t.last_status||'就绪');
    var prog=t.running&&t.total>0?(' '+t.done+'/'+t.total+' 张'):'';
    var last=t.last_run?('上次 '+esc(t.last_run)+' · '+esc(t.last_count)+' 张'):'尚未运行';
    var due=(!t.running&&t.enabled&&t.time===now)?' · 本分钟待触发':'';
    h+='<div class="api"><div class="name"><b>'+esc(t.name)+'</b> '
      +'<span class="badge">'+esc(t.time)+' · '+esc(dayLabel(t.days))+'</span></div>';
    h+='<div class="note">'+esc(st)+esc(prog)+' · '+(t.enabled?'已启用':'已停用')+' · '+zcfgLabel(t.cfg)+'</div>';
    h+='<div class="note">源：<code>'+esc((t.cfg&&t.cfg.src_dir)||'')+'</code></div>';
    h+='<div class="note">'+esc(last)+esc(due)+'</div>';
    if(t.error)h+='<div class="note warn">'+esc(t.error)+'</div>';
    h+='<div class="acts tacts">';
    h+='<button data-act="toggle" data-id="'+esc(t.id)+'">'+(t.enabled?'停用':'启用')+'</button>';
    h+='<button data-act="run" data-id="'+esc(t.id)+'"'+(t.running?' disabled':'')+'>立即运行</button>';
    h+='<button data-act="stop" data-id="'+esc(t.id)+'"'+(t.running?'':' disabled')+'>停止</button>';
    h+='<button data-act="edit" data-id="'+esc(t.id)+'">编辑</button>';
    h+='<button data-act="log" data-id="'+esc(t.id)+'">日志</button>';
    h+='<button data-act="delete" data-id="'+esc(t.id)+'">删除</button>';
    h+='</div></div>';
  }
  box.innerHTML=h;
}
function zDaysFrom(){var s='';for(var d=1;d<=7;d++)if(document.getElementById('zday'+d).checked)s+=String(d);return s;}
function zSetDays(s){s=s||'';for(var d=1;d<=7;d++)document.getElementById('zday'+d).checked=s.indexOf(String(d))>=0;}
function zCfgFromForm(){
  return {type:'compress',src_dir:val('z_src'),backup_dir:val('z_backup'),
    max_height:val('z_height'),max_size_mb:val('z_size'),
    q_max:val('z_qmax'),q_min:val('z_qmin'),
    to_jpg:document.getElementById('z_tojpg').checked?'1':'0',
    recursive:document.getElementById('z_rec').checked?'1':'0'};
}
function zFillForm(cfg){
  var map={z_src:'src_dir',z_backup:'backup_dir',z_height:'max_height',
    z_size:'max_size_mb',z_qmax:'q_max',z_qmin:'q_min'};
  for(var id in map){if(Object.prototype.hasOwnProperty.call(map,id)){
    var el=document.getElementById(id);if(el)el.value=cfg[map[id]]==null?'':cfg[map[id]];}}
  document.getElementById('z_tojpg').checked=String(cfg.to_jpg)!=='0';
  document.getElementById('z_rec').checked=String(cfg.recursive)==='1';
}
function zResetForm(){
  document.getElementById('z_name').value='';
  document.getElementById('z_time').value='03:00';
  document.getElementById('z_enabled').value='1';
  zSetDays('1234567');
  zFillForm(CDEF);
  zEditingId='';
}
var zEditingId='';
var knownTasks={};
/* 概览里的采集 / 压缩运行状态汇总（数据来自 /_tasks 轮询） */
function overviewTaskStatus(){
  var f={n:0,en:0,run:null,last:null},z={n:0,en:0,run:null,last:null};
  for(var id in knownTasks){var t=knownTasks[id],isZip=(t.type==='compress'),g=isZip?z:f;
    g.n++;if(t.enabled)g.en++;
    if(t.running&&!g.run)g.run=t;
    if(t.last_run&&(!g.last||t.last_run>g.last.last_run))g.last=t;
  }
  function text(g,isZip,doing){
    var e=document.getElementById(isZip?'ovZip':'ovFetch');if(!e)return;
    if(g.run){e.className='v ok';e.textContent=doing+' · '+(g.run.done||0)+'/'+(g.run.total||0);return;}
    if(!g.n){e.className='v';e.textContent='无任务';return;}
    var s=g.en+' 启用 / '+g.n+' 个',dict=isZip?ZSTATUS:TSTATUS;
    if(g.last&&g.last.last_status)s+=' · '+(dict[g.last.last_status]||g.last.last_status);
    e.className='v';e.textContent=s;
  }
  text(f,false,'采集中');text(z,true,'压缩中');
}
function poll(){
  fetch(BASE+'/_tasks',{cache:'no-store'})
   .then(function(r){return r.json()}).then(function(j){
     if(!j.ok)return;
     applyKeyState(j.api_key_set);
     knownTasks={};for(var i=0;i<j.tasks.length;i++)knownTasks[j.tasks[i].id]=j.tasks[i];
     renderTasks(j.tasks,j.now);
     renderZipTasks(j.tasks,j.now);
     overviewTaskStatus();
     var running=null,zipRunning=null;
     for(var id in knownTasks){var tk=knownTasks[id];if(tk.running){
       if(tk.type==='compress'){if(!zipRunning)zipRunning=tk;}
       else if(!running)running=tk;}}
     if(running){
       var box=document.getElementById('tlog');box.style.display='block';
       box.textContent=(running.log||[]).join(String.fromCharCode(10));box.scrollTop=box.scrollHeight;
     }
     if(zipRunning){
       var zbox=document.getElementById('zlog');zbox.style.display='block';
       zbox.textContent=(zipRunning.log||[]).join(String.fromCharCode(10));zbox.scrollTop=zbox.scrollHeight;
     }
     setTimeout(poll,3000);
   }).catch(function(){setTimeout(poll,5000)});
}
document.getElementById('tasklist').addEventListener('click',function(e){
  var b=e.target.closest('button[data-act]');if(!b)return;
  var act=b.getAttribute('data-act'),id=b.getAttribute('data-id'),t=knownTasks[id];
  if(act==='edit'&&t){
    editingId=id;
    document.getElementById('t_name').value=t.name;
    document.getElementById('t_time').value=t.time;
    document.getElementById('t_enabled').value=t.enabled?'1':'0';
    setDays(t.days||'');
    fillForm(t.cfg||TDEF);
    document.getElementById('tformbox').open=true;
    document.getElementById('t_name').scrollIntoView({block:'center'});
    clearMsg();
  }else if(act==='log'&&t){
    var box=document.getElementById('tlog');box.style.display='block';
    box.textContent=(t.log&&t.log.length)?t.log.join(String.fromCharCode(10)):'（暂无日志）';
  }else if(act==='delete'){
    if(!window.confirm('确定删除这个采集任务？'))return;
    tpost('/_tasks/delete',{id:id},function(j){
      if(j.ok){tmsg('任务已删除','ok');poll();}else tmsg(j.error||'删除失败','warn');});
  }else if(act==='toggle'){
    tpost('/_tasks/toggle',{id:id},function(j){if(j.ok)poll();else tmsg(j.error||'操作失败','warn');});
  }else if(act==='run'){
    clearMsg();tpost('/_tasks/run',{id:id},function(j){if(j.ok){tmsg('任务已加入执行队列','ok');poll();}else tmsg(j.error||'启动失败','warn');});
  }else if(act==='stop'){
    tpost('/_tasks/stop',{id:id},function(j){if(j.ok)poll();else tmsg(j.error||'停止失败','warn');});
  }
});
document.getElementById('tnew').onclick=function(){resetForm();document.getElementById('tformbox').open=true;clearMsg();document.getElementById('t_name').scrollIntoView({block:'center'});};
document.getElementById('tcancel').onclick=function(){resetForm();document.getElementById('tformbox').open=false;clearMsg();};
document.getElementById('tsave').onclick=function(){
  var btn=this;btn.disabled=true;clearMsg();
  var body=tcfgFromForm();
  body.id=editingId;
  body.name=val('t_name');
  body.time=val('t_time');
  body.days=daysFrom();
  body.enabled=val('t_enabled');
  tpost('/_tasks/save',body,function(j){
    btn.disabled=false;
    if(!j.ok){tmsg('保存失败：'+(j.error||'未知错误'),'warn');return;}
    tmsg('任务已保存','ok');resetForm();document.getElementById('tformbox').open=false;poll();
  });
};
function zmsg(text,kind){
  var el=document.getElementById('zmsg');el.textContent=text;
  el.className='cfgmsg show'+(kind?' '+kind:'');
}
function zclearMsg(){document.getElementById('zmsg').className='cfgmsg';}
document.getElementById('zlist').addEventListener('click',function(e){
  var b=e.target.closest('button[data-act]');if(!b)return;
  var act=b.getAttribute('data-act'),id=b.getAttribute('data-id'),t=knownTasks[id];
  if(act==='edit'&&t){
    zEditingId=id;
    document.getElementById('z_name').value=t.name;
    document.getElementById('z_time').value=t.time;
    document.getElementById('z_enabled').value=t.enabled?'1':'0';
    zSetDays(t.days||'');
    zFillForm(t.cfg||CDEF);
    document.getElementById('zformbox').open=true;
    document.getElementById('z_name').scrollIntoView({block:'center'});
    zclearMsg();
  }else if(act==='log'&&t){
    var box=document.getElementById('zlog');box.style.display='block';
    box.textContent=(t.log&&t.log.length)?t.log.join(String.fromCharCode(10)):'（暂无日志）';
  }else if(act==='delete'){
    if(!window.confirm('确定删除这个压缩任务？'))return;
    tpost('/_tasks/delete',{id:id},function(j){
      if(j.ok){zmsg('任务已删除','ok');poll();}else zmsg(j.error||'删除失败','warn');});
  }else if(act==='toggle'){
    tpost('/_tasks/toggle',{id:id},function(j){if(j.ok)poll();else zmsg(j.error||'操作失败','warn');});
  }else if(act==='run'){
    zclearMsg();tpost('/_tasks/run',{id:id},function(j){if(j.ok){zmsg('任务已加入执行队列','ok');poll();}else zmsg(j.error||'启动失败','warn');});
  }else if(act==='stop'){
    tpost('/_tasks/stop',{id:id},function(j){if(j.ok)poll();else zmsg(j.error||'停止失败','warn');});
  }
});
document.getElementById('znew').onclick=function(){zResetForm();document.getElementById('zformbox').open=true;zclearMsg();document.getElementById('z_name').scrollIntoView({block:'center'});};
document.getElementById('zcancel').onclick=function(){zResetForm();document.getElementById('zformbox').open=false;zclearMsg();};
document.getElementById('zsave').onclick=function(){
  var btn=this;btn.disabled=true;zclearMsg();
  var body=zCfgFromForm();
  body.id=zEditingId;
  body.name=val('z_name');
  body.time=val('z_time');
  body.days=zDaysFrom();
  body.enabled=val('z_enabled');
  tpost('/_tasks/save',body,function(j){
    btn.disabled=false;
    if(!j.ok){zmsg('保存失败：'+(j.error||'未知错误'),'warn');return;}
    zmsg('任务已保存','ok');zResetForm();document.getElementById('zformbox').open=false;poll();
  });
};
poll();
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
            acts = ('<a class="pv" href="%s/%s" data-p="%s" data-n="%d" target="_blank">打开看看</a>'
                    '<button class="cp" data-p="%s">复制地址</button>'
                    % (html.escape(base), html.escape(encoded),
                       html.escape(encoded), count, html.escape(encoded)))
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
    # New-task defaults follow the table: 0 = unlimited/random, Hot sorting.
    # The API key is global and never echoed into the task form.
    tdef = json.dumps(FETCH_DEFAULTS, ensure_ascii=False)
    cdef = json.dumps(COMPRESS_DEFAULTS, ensure_ascii=False)
    return PAGE.substitute(
        title=APP_TITLE, version=VERSION, port=cfg["port"], tdef=tdef, cdef=cdef,
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

    def _fetch_form(self, form):
        def val(key):
            return (form.get(key) or [""])[0].strip()
        raw = {key: val(key) for key in FETCH_DEFAULTS}
        # The API key is never echoed back into the page. An empty field means
        # "keep the stored one"; otherwise saving other settings would wipe it.
        if not raw.get("api_key"):
            raw["api_key"] = load_fetch_config().get("api_key", "")
        cfg, err = fetch_valid(raw)
        if cfg:
            apply_global_key(cfg)
        return cfg, err

    def handle_fetch_config(self, form):
        cfg, err = self._fetch_form(form)
        if err:
            return self.send_json({"ok": False, "error": err}, 400)
        try:
            save_fetch_config(cfg)
        except OSError as exc:
            return self.send_json({"ok": False, "error": "配置写入失败：%s" % exc}, 500)
        return self.send_json({"ok": True})

    def handle_fetch_start(self, form):
        cfg, err = self._fetch_form(form)
        if err:
            return self.send_json({"ok": False, "error": err}, 400)
        with _fetch_lock:
            if _fetch_state["running"]:
                return self.send_json({"ok": False, "error": "已有采集任务在运行"}, 409)
        try:
            save_fetch_config(cfg)
        except OSError as exc:
            return self.send_json({"ok": False, "error": "配置写入失败：%s" % exc}, 500)
        _cancel.clear()
        _fetch_set(running=True, phase="running", done=0, total=cfg["count"],
                   page=0, error="", started=time.time(), finished=0, log=[])
        threading.Thread(target=wh_collect, args=(cfg,), daemon=True).start()
        with _fetch_lock:
            snap = {k: list(v) if k == "log" else v for k, v in _fetch_state.items()}
        return self.send_json({"ok": True, "state": snap})

    def handle_fetch_stop(self):
        _cancel.set()
        with _fetch_lock:
            snap = {k: list(v) if k == "log" else v for k, v in _fetch_state.items()}
        return self.send_json({"ok": True, "state": snap})

    def _form_val(self, form, key):
        return (form.get(key) or [""])[0].strip()

    def handle_tasks_get(self):
        with _tasks_lock:
            items = [task_public(t) for t in _tasks]
        key_set = bool(load_fetch_config().get("api_key"))
        return self.send_json({"ok": True, "tasks": items,
                               "now": time.strftime("%H:%M"),
                               "weekday": str(time.localtime().tm_wday + 1),
                               "api_key_set": key_set, "sfw_only": not key_set})

    def handle_api_key(self, form):
        """Global API Key. Blank means Wallhaven SFW-only (table rule)."""
        key = self._form_val(form, "api_key")
        fc = load_fetch_config()
        fc["api_key"] = key
        try:
            save_fetch_config(fc)
        except OSError as exc:
            return self.send_json({"ok": False, "error": "写入失败：%s" % exc}, 500)
        with _tasks_lock:
            for t in _tasks:
                t["cfg"] = apply_global_key(t["cfg"])
        save_tasks()
        return self.send_json({
            "ok": True, "api_key_set": bool(key),
            "message": ("API Key 已保存，含 Sketchy / NSFW 的筛选会生效" if key
                        else "已清空 API Key，所有任务强制仅下载 SFW"),
        })

    def handle_tasks_save(self, form):
        tid = self._form_val(form, "id")
        name = self._form_val(form, "name")
        tm = valid_time(self._form_val(form, "time"))
        if not name:
            return self.send_json({"ok": False, "error": "任务名称不能为空"}, 400)
        if not tm:
            return self.send_json({"ok": False, "error": "执行时刻格式应为 HH:MM（00:00-23:59）"}, 400)
        kind = self._form_val(form, "type") or "fetch"
        if kind not in ("fetch", "compress"):
            kind = "fetch"
        if kind == "compress":
            raw = {k: self._form_val(form, k) for k in COMPRESS_DEFAULTS}
            cfg, err = compress_valid(raw)
        else:
            raw = {k: self._form_val(form, k) for k in FETCH_DEFAULTS}
            cfg, err = fetch_valid(raw)
            if not err:
                cfg = apply_global_key(cfg)   # global key; blank key -> SFW only
        if err:
            return self.send_json({"ok": False, "error": err}, 400)
        if "days" in form:
            days = valid_days(self._form_val(form, "days"))
        else:                            # legacy client sending only `loop`
            days = ("1234567" if self._form_val(form, "loop")
                    in ("1", "true", "on", "yes") else "")
        enabled = self._form_val(form, "enabled") in ("1", "true", "on", "yes")
        with _tasks_lock:
            if tid:
                t = next((x for x in _tasks if x["id"] == tid), None)
                if not t:
                    return self.send_json({"ok": False, "error": "任务不存在"}, 404)
                t.update(name=name, time=tm, days=days, cfg=cfg, enabled=enabled, type=kind)
            else:
                tid = new_task_id()
                _tasks.append({"id": tid, "type": kind, "name": name, "enabled": enabled,
                               "time": tm, "days": days, "last_run": "",
                               "last_status": "idle", "last_count": 0, "cfg": cfg})
                task_rt(tid)
        save_tasks()
        with _tasks_lock:
            t = next(x for x in _tasks if x["id"] == tid)
            return self.send_json({"ok": True, "task": task_public(t)})

    def handle_tasks_delete(self, form):
        tid = self._form_val(form, "id")
        with _tasks_lock:
            before = len(_tasks)
            _tasks[:] = [x for x in _tasks if x["id"] != tid]
            if len(_tasks) == before:
                return self.send_json({"ok": False, "error": "任务不存在"}, 404)
            _task_rt.pop(tid, None)
        save_tasks()
        return self.send_json({"ok": True})

    def handle_image_delete(self, form):
        cat = self._form_val(form, "cat")
        try:
            idx = int(self._form_val(form, "i") or "0")
        except ValueError:
            idx = 0
        ok, payload = delete_preview_image(cat, idx)
        if not ok:
            return self.send_json({"ok": False, "error": payload}, 400)
        return self.send_json(payload)

    def handle_image_magician(self, form):
        ok, payload = sweep_missing_blacklist()
        if not ok:
            return self.send_json({"ok": False, "error": payload}, 400)
        return self.send_json(payload)

    def handle_tasks_toggle(self, form):
        tid = self._form_val(form, "id")
        with _tasks_lock:
            t = next((x for x in _tasks if x["id"] == tid), None)
            if not t:
                return self.send_json({"ok": False, "error": "任务不存在"}, 404)
            t["enabled"] = not t["enabled"]
            enabled = t["enabled"]
        save_tasks()
        return self.send_json({"ok": True, "enabled": enabled})

    def handle_tasks_run(self, form):
        tid = self._form_val(form, "id")
        with _tasks_lock:
            t = next((x for x in _tasks if x["id"] == tid), None)
            if not t:
                return self.send_json({"ok": False, "error": "任务不存在"}, 404)
            rt = task_rt(tid)
            busy = rt["running"]
        if busy:
            return self.send_json({"ok": False, "error": "该任务正在运行"}, 409)
        _task_queue.put(tid)
        return self.send_json({"ok": True})

    def handle_tasks_stop(self, form):
        tid = self._form_val(form, "id")
        with _tasks_lock:
            rt = _task_rt.get(tid)
            if not rt or not rt["running"]:
                return self.send_json({"ok": False, "error": "该任务未在运行"}, 409)
            rt["cancel"].set()
        return self.send_json({"ok": True})

    def handle_tasks_status(self, form):
        tid = self._form_val(form, "id")
        with _tasks_lock:
            t = next((x for x in _tasks if x["id"] == tid), None)
            if not t:
                return self.send_json({"ok": False, "error": "任务不存在"}, 404)
            return self.send_json({"ok": True, "task": task_public(t)})

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
        if path == "/_tasks":
            return self.handle_tasks_get()
        if path == "/_fetch_status":
            with _fetch_lock:
                snap = {k: (list(v) if k == "log" else v)
                        for k, v in _fetch_state.items()}
            snap["ok"] = True
            return self.send_json(snap)
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
        # Preview wants newest-downloaded first, walked in order; the plain URL
        # (used by copy-link and third parties) stays random. order=recent&i=N
        # selects the N-th item sorted by file mtime descending.
        query = parse_qs(urlparse(self.path).query)
        if query.get("order") == ["recent"]:
            def _mtime(p):
                try:
                    return os.path.getmtime(p)
                except OSError:
                    return 0.0
            ordered = sorted(cats[canonical], key=lambda p: (_mtime(p), p), reverse=True)
            try:
                idx = int(query.get("i", ["0"])[0])
            except (ValueError, IndexError):
                idx = 0
            return self.send_image(ordered[idx % len(ordered)])
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
            if path == "/_api_key":
                return self.handle_api_key(form)
            if path == "/_reload":
                return self.handle_reload()
            if path == "/_image/delete":
                return self.handle_image_delete(form)
            if path == "/_image/magician":
                return self.handle_image_magician(form)
            if path == "/_tasks/save":
                return self.handle_tasks_save(form)
            if path == "/_tasks/delete":
                return self.handle_tasks_delete(form)
            if path == "/_tasks/toggle":
                return self.handle_tasks_toggle(form)
            if path == "/_tasks/run":
                return self.handle_tasks_run(form)
            if path == "/_tasks/stop":
                return self.handle_tasks_stop(form)
            if path == "/_tasks/status":
                return self.handle_tasks_status(form)
            if path == "/_fetch_start":
                return self.handle_fetch_start(form)
            if path == "/_fetch_stop":
                return self.handle_fetch_stop()
            if path == "/_fetch_config":
                return self.handle_fetch_config(form)
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
    start_tasks()
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
        _sched_stop.set()
        _cancel.set()
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
