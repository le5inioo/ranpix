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

import hashlib
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
VERSION = "2.2.0"
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


def valid_theme(value):
    return value if value in ("auto", "light", "dark") else "auto"


def load_config():
    cfg = {"image_root": "", "port": DEFAULT_PORT, "cache_ttl": 30, "theme": "auto",
           "cleanup_uploads": 0}
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
    cfg["theme"] = valid_theme(cfg.get("theme"))
    return cfg


def save_config(cfg):
    with open(CONFIG_PATH, "w", encoding="utf-8") as fh:
        json.dump({"image_root": cfg.get("image_root", ""),
                   "port": cfg["port"],
                   "cache_ttl": cfg["cache_ttl"],
                   "theme": valid_theme(cfg.get("theme")),
                   "cleanup_uploads": 1 if cfg.get("cleanup_uploads") else 0}, fh,
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


def add_downloaded_records(folder, wids):
    """把采集图 ID 登记到指定目录的 downloaded.txt（幂等、去重、大小写不敏感）。

    downloaded.txt 的语义 = 所在文件夹的图片索引：压缩备份把采集图复制进备份
    目录时，必须同步把 ID 写进该目录自己的索引，保持索引与文件一致。
    自传图取不到 ID，不写。Returns 实际新增的记录条数。
    """
    ids = {str(w).strip().lower() for w in wids if str(w or "").strip()}
    if not ids:
        return 0
    state = os.path.join(folder, "downloaded.txt")
    try:
        with open(state, "r", encoding="utf-8") as fh:
            lines = fh.readlines()
    except OSError:
        lines = []
    have = {ln.strip().lower() for ln in lines if ln.strip()}
    add = sorted(ids - have)
    if not add:
        return 0
    tmp = state + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as fh:
            for ln in lines:
                fh.write(ln if ln.endswith("\n") else ln + "\n")
            for w in add:
                fh.write(w + "\n")
        os.replace(tmp, state)
        return len(add)
    except OSError:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        return 0


def remove_downloaded_records(wids):
    """从所有分类（含压缩备份目录）的 downloaded.txt 中批量移除采集图 ID。

    downloaded.txt 的语义 = 所在文件夹的当前图片名单：删图/补拉黑后必须同步
    移除对应记录，避免「有记录无文件」的历史噪音。自传图无 ID，不受影响。
    Returns 实际移除的记录条数。
    """
    ids = {str(w).strip().lower() for w in wids if str(w or "").strip()}
    if not ids:
        return 0
    root = load_config()["image_root"]
    removed = 0
    folders = []
    for name in categories():
        folders.append(os.path.join(root, name) if name else root)
    for folder in backup_folders():
        if folder and folder not in folders:
            folders.append(folder)
    for folder in folders:
        state = os.path.join(folder, "downloaded.txt")
        try:
            with open(state, "r", encoding="utf-8") as fh:
                lines = fh.readlines()
        except OSError:
            continue
        keep = [ln for ln in lines if ln.strip().lower() not in ids]
        if len(keep) == len(lines):
            continue
        tmp = state + ".tmp"
        try:
            with open(tmp, "w", encoding="utf-8") as fh:
                fh.writelines(keep)
            os.replace(tmp, state)
            removed += len(lines) - len(keep)
        except OSError:
            try:
                os.unlink(tmp)
            except OSError:
                pass
    return removed


# 自传图指纹墓碑：独立文件，绝不与采集图 ID 黑名单混用。
# 只有开启「清理自传图」开关后，删除自传图时才会写入其 SHA-256，
# 供删图联动与魔术师全局清理按内容识别同一张自传图的所有副本。
UPLOAD_HASH_PATH = os.path.join(ETC_DIR, "upload_hashes.json")
_upload_hash_lock = threading.RLock()


def file_sha256(path):
    """Return the SHA-256 hex digest of a file's bytes (streamed)."""
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def load_upload_hashes():
    with _upload_hash_lock:
        try:
            with open(UPLOAD_HASH_PATH, "r", encoding="utf-8") as fh:
                data = json.load(fh)
            if isinstance(data, dict):
                data = data.get("hashes")
            if isinstance(data, list):
                return {str(x).strip().lower() for x in data if str(x).strip()}
        except (OSError, ValueError):
            pass
        return set()


def save_upload_hashes(hashes):
    with _upload_hash_lock:
        tmp = UPLOAD_HASH_PATH + ".tmp"
        with open(tmp, "w", encoding="utf-8") as fh:
            json.dump({"hashes": sorted(hashes)}, fh, ensure_ascii=False, indent=2)
        os.replace(tmp, UPLOAD_HASH_PATH)
        try:
            os.chmod(UPLOAD_HASH_PATH, 0o666)
        except OSError:
            pass


def add_upload_hash(path):
    """立墓碑：记录一张自传图的内容指纹。返回 (digest, is_new)。"""
    digest = file_sha256(path)
    with _upload_hash_lock:
        hashes = load_upload_hashes()
        is_new = digest not in hashes
        if is_new:
            hashes.add(digest)
            save_upload_hashes(hashes)
    return digest, is_new


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
    # 全局判定：只要任一分类目录还有同 ID 文件，就不算「外部删除」。
    # 用全局索引而非「当前分类的 paths」，避免把用户用文件管理器移动到别的
    # 分类的采集图误判成已删除 -> 误拉黑 -> 又被全局清理删掉原件。
    # 注意只看分类（tag != None）：压缩备份目录里的副本是待清理对象，不能
    # 当作原件仍存在的证据，否则外部删掉的图会永远留在备份目录无法收敛。
    global_present = set()
    for _wid, entries in wid_index().items():
        if any(tag is not None for _p, tag in entries):
            global_present.add(_wid)
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
        missing |= (recorded - global_present)

    added = 0
    for wid in sorted(missing):
        if add_blacklist(wid):
            added += 1
    # 同步移除失效记录：downloaded.txt = 当前存在的图片名单，文件不在了记录也删。
    # 已拉黑但残留的旧记录同样清掉，避免历史噪音一直挂在体检里。
    records_removed = remove_downloaded_records(missing)
    log("magic sweep: %d recorded IDs, %d missing, %d newly blacklisted, "
        "%d stale records removed"
        % (scanned, len(missing), added, records_removed))
    return True, {"ok": True, "scanned": scanned, "missing": len(missing),
                  "added": added, "records_removed": records_removed,
                  "total": len(load_blacklist())}


def consistency_check():
    """只读体检：统计索引/删除/拉黑三者的偏差，绝不修改任何文件。

    Returns:
      in_blacklist_with_file: 已进黑名单但分类里仍有文件的 ID（等待魔术师清理）
      recorded_no_file: downloaded.txt 有记录但所有分类都无文件的 ID（sweep 会补拉黑并清理记录）
      file_no_record: 分类里有采集图但没有任何 downloaded.txt 记录该 ID
      blacklist_total / recorded_total / collected_files: 规模参考
    """
    cfg = load_config()
    root = cfg["image_root"]
    cats = categories()
    blacklist = load_blacklist()

    # 分类里现存的采集图 ID 集合（不含压缩备份目录）
    files_by_wid = {}
    for name, paths in cats.items():
        for p in paths:
            wid = image_wid(p)
            if wid:
                files_by_wid.setdefault(wid, []).append(p)
    present = set(files_by_wid)

    # 所有分类 downloaded.txt 的记录合集
    recorded = set()
    for name in cats:
        folder = os.path.join(root, name) if name else root
        try:
            with open(os.path.join(folder, "downloaded.txt"), "r",
                      encoding="utf-8") as fh:
                recorded.update(line.strip().lower() for line in fh if line.strip())
        except OSError:
            pass

    in_blacklist_with_file = sorted(blacklist & present)
    recorded_no_file = sorted(recorded - present)
    file_no_record = sorted(present - recorded)

    # 备份目录里黑名单命中的 ID（魔术师全局清理的另一处目标）
    backup_hits = 0
    for wid, entries in wid_index().items():
        if wid in blacklist and any(tag is None for _p, tag in entries):
            backup_hits += 1

    return {
        "ok": True,
        "in_blacklist_with_file": len(in_blacklist_with_file),
        "recorded_no_file": len(recorded_no_file),
        "file_no_record": len(file_no_record),
        "backup_blacklist_hits": backup_hits,
        "blacklist_total": len(blacklist),
        "recorded_total": len(recorded),
        "collected_files": sum(len(v) for v in files_by_wid.values()),
        "samples": {
            "in_blacklist_with_file": in_blacklist_with_file[:8],
            "recorded_no_file": recorded_no_file[:8],
            "file_no_record": file_no_record[:8],
        },
    }


def purge_blacklisted_in_category(category):
    """批量删除当前分类里所有 ID 已进入全局黑名单的采集图。

    只处理文件名形如 wallhaven-<id>.<ext> 的采集图（image_wid 能取到 ID）；
    用户自己上传的图片取不到 ID，绝不会被删。Returns (ok, payload).
    """
    cats = categories()
    canonical, _amb = resolve_category(category, cats)
    if canonical is None:
        return False, "分类不存在"
    paths = cats.get(canonical) or []
    blacklist = load_blacklist()
    removed = 0
    failed = 0
    for p in list(paths):
        wid = image_wid(p)
        if not wid or wid not in blacklist:
            continue
        try:
            os.unlink(p)
            removed += 1
        except OSError:
            failed += 1
    if removed:
        _cache["ts"] = 0.0                  # force rescan to see deletions
    remaining = len(categories().get(canonical) or [])
    log("magic purge %s: %d removed, %d failed" % (canonical, removed, failed))
    return True, {"ok": True, "removed": removed, "failed": failed,
                  "remaining": remaining}


def purge_blacklisted_everywhere(category=None, cleanup_uploads=None):
    """魔术师全局清理：删除所有目录里黑名单命中的采集图；开关开时再清自传图。

    采集图按 wid 索引命中黑名单删除；自传图（取不到 ID）在 cleanup_uploads
    开启时按指纹墓碑删除，关闭时一律不碰。两条链路互不重叠。
    category 仅用于单独统计当前接口分类删了几张，方便前端修正 x/xx。
    Returns (ok, payload).
    """
    cats = categories()
    canonical = None
    if category:
        canonical, _amb = resolve_category(category, cats)
        if canonical is None:
            return False, "分类不存在"
    if cleanup_uploads is None:
        cleanup_uploads = bool(load_config().get("cleanup_uploads"))
    blacklist = load_blacklist()
    removed = failed = in_cat = in_backup = 0
    seen = set()
    purged_wids = set()
    for wid, entries in wid_index().items():
        if wid not in blacklist:
            continue
        for path, tag in entries:
            real = os.path.abspath(path)
            if real in seen:
                continue
            seen.add(real)
            if not os.path.isfile(path):
                continue
            try:
                os.unlink(path)
                removed += 1
                # 删了采集图副本就登记清记录（含备份目录副本）：索引 =
                # 文件夹现存名单，副本没了对应目录的记录也要跟着清。
                purged_wids.add(wid)
                if canonical is not None and tag == canonical:
                    in_cat += 1
                if tag is None:
                    in_backup += 1
            except OSError:
                failed += 1
    # 同步移除被删采集图的下载记录（含备份目录副本，索引 = 文件夹现存名单）
    records_removed = remove_downloaded_records(purged_wids)

    # 自传图：开关打开时，按指纹墓碑删除所有内容命中的自传图副本
    up_removed = up_failed = up_cat = up_backup = 0
    if cleanup_uploads:
        hashes = load_upload_hashes()
        for digest in sorted(hashes):
            r, f, c, b = purge_hash_everywhere(digest, canonical)
            up_removed += r; up_failed += f; up_cat += c; up_backup += b
        if up_removed:
            _cache["ts"] = 0.0

    scanned = len(cats) + len(backup_folders())
    if removed or up_removed:
        _cache["ts"] = 0.0
    remaining = len(categories().get(canonical) or []) if canonical else 0
    log("magic purge all: %d uploaded + %d collected removed "
        "(%d in current category, %d in backup), %d failed, %d dirs"
        % (up_removed, removed, in_cat + up_cat, in_backup + up_backup,
           failed + up_failed, scanned))
    return True, {"ok": True, "removed": removed + up_removed,
                  "collected_removed": removed, "upload_removed": up_removed,
                  "records_removed": records_removed,
                  "failed": failed + up_failed,
                  "scanned_dirs": scanned,
                  "in_category": in_cat + up_cat,
                  "in_backup": in_backup + up_backup,
                  "remaining": remaining,
                  "cleanup_uploads": bool(cleanup_uploads)}


def purge_wid_everywhere(wid, canonical=None):
    """删除指定 wallhaven ID 在所有分类目录和备份目录里的副本。

    走 wid_index() 内存索引按 ID 直接定位，不再逐个目录 listdir。
    只认 wallhaven-<id> 命名的采集图；自传图取不到 ID，绝不会被删。
    canonical 用于单独统计当前接口分类里额外删了几张，方便前端修正 x/xx。
    Returns (removed, failed, scanned_dirs, in_category, in_backup).
    """
    wid = str(wid or "").strip().lower()
    if not wid:
        return 0, 0, 0, 0, 0
    removed = failed = in_cat = in_backup = 0
    seen = set()
    for path, tag in wid_index().get(wid, []):
        real = os.path.abspath(path)
        if real in seen:
            continue
        seen.add(real)
        if not os.path.isfile(path) or image_wid(path) != wid:
            continue
        try:
            os.unlink(path)
            removed += 1
            if canonical is not None and tag == canonical:
                in_cat += 1
            if tag is None:
                in_backup += 1
        except OSError:
            failed += 1

    scanned = len(categories()) + len(backup_folders())
    if removed:
        _cache["ts"] = 0.0
    log("sync delete wid=%s: %d copies removed (%d in category, %d in backup), "
        "%d failed, %d dirs" % (wid, removed, in_cat, in_backup, failed, scanned))
    return removed, failed, scanned, in_cat, in_backup


def all_image_paths():
    """所有图库路径 + 压缩备份目录路径，元素为 (path, tag)；tag=None 表示备份目录。"""
    out = []
    for name, plist in categories().items():
        for p in plist:
            out.append((p, name))
    for folder in backup_folders():
        try:
            for n in os.listdir(folder):
                fp = os.path.join(folder, n)
                if os.path.isfile(fp):
                    out.append((fp, None))
        except OSError:
            pass
    return out


def purge_hash_everywhere(target_digest, canonical=None, skip=None):
    """删除所有目录里内容与 target_digest 相同的自传图（不含采集图、不含 skip 路径）。

    只处理取不到 wallhaven ID 的自传图：采集图一律走 wid 链路，避免混用两套墓碑。
    Returns (removed, failed, in_category, in_backup).
    """
    target_digest = str(target_digest or "").strip().lower()
    if not target_digest:
        return 0, 0, 0, 0
    skip = os.path.abspath(skip) if skip else None
    removed = failed = in_cat = in_backup = 0
    seen = set()
    for path, tag in all_image_paths():
        real = os.path.abspath(path)
        if real in seen or (skip and real == skip):
            continue
        seen.add(real)
        if image_wid(path):            # 采集图只走 wid 链路
            continue
        if not os.path.isfile(path):
            continue
        try:
            if file_sha256(path) != target_digest:
                continue
            os.unlink(path)
            removed += 1
            if canonical is not None and tag == canonical:
                in_cat += 1
            if tag is None:
                in_backup += 1
        except OSError:
            failed += 1
    if removed:
        _cache["ts"] = 0.0
    log("sync delete upload hash=%s: %d copies removed (%d in category, %d in backup), "
        "%d failed" % (target_digest[:12], removed, in_cat, in_backup, failed))
    return removed, failed, in_cat, in_backup


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
    # 先立墓碑再删文件：写墓碑是幂等的原子落盘，一旦失败就中止删除，
    # 避免出现「文件已删、ID/指纹没进墓碑」导致残留副本无法被清理的偏差。
    digest = ""
    if wid:
        try:
            add_blacklist(wid)
        except OSError as exc:
            return False, "写入黑名单失败，已取消删除：%s" % exc
    elif load_config().get("cleanup_uploads"):
        # 自传图：仅在开关打开时按内容指纹立墓碑并联动清理相同副本
        try:
            digest, _new = add_upload_hash(target)
        except OSError as exc:
            return False, "写入指纹墓碑失败，已取消删除：%s" % exc
    try:
        os.unlink(target)
    except OSError as exc:
        return False, "删除失败：%s" % exc
    # 联动前强制刷新缓存，让索引重扫并把文件管理器外部新增的副本也纳入。
    # target 已按刷新前的预览序号锁定，刷新不会换掉删除目标。
    _cache["ts"] = 0.0
    synced = sync_failed = sync_dirs = sync_cat = sync_backup = 0
    up_synced = up_failed = up_cat = up_backup = 0
    records_removed = 0
    if wid:
        synced, sync_failed, sync_dirs, sync_cat, sync_backup = \
            purge_wid_everywhere(wid, canonical)
        records_removed = remove_downloaded_records([wid])
    elif digest:
        up_synced, up_failed, up_cat, up_backup = \
            purge_hash_everywhere(digest, canonical, skip=target)
    _cache["ts"] = 0.0                  # refresh gallery scan immediately
    log("deleted image: %s (wid=%s or hash=%s, synced=%d/%d)"
        % (target, wid or "n/a", digest[:12] or "n/a", synced, up_synced))
    return True, {"ok": True, "deleted": name, "wid": wid,
                  "blacklisted": bool(wid), "records_removed": records_removed,
                  "synced": synced + up_synced,
                  "synced_failed": sync_failed + up_failed,
                  "synced_dirs": sync_dirs,
                  "synced_cat": sync_cat + up_cat,
                  "synced_backup": sync_backup + up_backup}


def _mtime_of(p):
    try:
        return os.path.getmtime(p)
    except OSError:
        return 0.0


def preview_image_label(category, index):
    """左下角角标文案：采集图显示 wallhaven ID，自传图显示文件名前 6 个字符。

    排序严格镜像 route() 里的 order=recent&i=N，保证角标与当前预览图一致。
    """
    cats = categories()
    canonical, _amb = resolve_category(category, cats)
    if canonical is None or not cats.get(canonical):
        return ""
    ordered = sorted(cats[canonical], key=lambda p: (_mtime_of(p), p), reverse=True)
    if not ordered:
        return ""
    target = ordered[index % len(ordered)]      # 与预览一致：末尾回绕
    wid = image_wid(target)
    if wid:
        return wid
    return os.path.basename(target)[:6]


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


# wid -> [(path, tag)] 内存索引。tag 为分类名，None 表示压缩备份目录。
# 随 _cache 刷新自动重建：不需要额外持久化文件，也不必在采集/压缩/上传等
# 写入点维护；所有 _cache["ts"]=0 的强制刷新点都会让它跟着更新。
_wid_index = {"ts": None, "root": None, "paths": {}}


def backup_folders():
    """从压缩任务配置取所有 backup_dir（该字段在 tasks.json，不在 config.json）。"""
    folders = []
    try:
        for t in list(_tasks):
            if t.get("type") == "compress":
                folder = (t.get("cfg") or {}).get("backup_dir", "")
                if folder and folder not in folders:
                    folders.append(folder)
    except Exception:
        pass
    return folders


def wid_index():
    """返回 {wid: [(path, tag), ...]}，删除时按 ID 直接定位副本。

    缓存有效时纯字典查找，不读配置、不列目录；仅缓存失效才重建。
    """
    if (_wid_index["ts"] is None or
            _wid_index["ts"] != _cache["ts"] or
            _wid_index["root"] != _cache["root"]):
        cats = categories()
        paths = {}
        for name, plist in cats.items():
            for p in plist:
                wid = image_wid(p)
                if wid:
                    paths.setdefault(wid, []).append((p, name))
        for folder in backup_folders():
            if not os.path.isdir(folder):
                continue
            try:
                names = os.listdir(folder)
            except OSError:
                continue
            for n in names:
                p = os.path.join(folder, n)
                if not os.path.isfile(p):
                    continue
                wid = image_wid(p)
                if wid:
                    paths.setdefault(wid, []).append((p, None))
        _wid_index["paths"] = paths
        _wid_index["ts"] = _cache["ts"]
        _wid_index["root"] = _cache["root"]
    return _wid_index["paths"]


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
    "end_page": 0,             # 0 = unlimited（实际翻页上限见 G["max_page_span"] 跨度）
    "min_favorites": 0,        # 0 = any
    "min_size_kb": 0,          # 0 = any
    "max_size_mb": 0,          # 0 = any
    "query": "",
    "clear_before": 0,         # 1 = empty the target category folder before collecting
    "max_pages": 500,          # 兼容旧字段，不再用于翻页（跨度上限见 G["max_page_span"]）
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
    for key, lo, hi in (("count", 1, 480), ("min_favorites", 0, 100000),
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
    "full_backup": 0,          # 1 = back up every image (not just ones needing compression)
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
    for key in ("to_jpg", "recursive", "full_backup"):
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


class _FetchCancelled(Exception):
    """Raised inside a blocking network read when the task is cancelled."""


def wh_request(url, api_key="", timeout=60, ctx=None):
    """Fetch bytes from wallhaven.

    When ctx is provided, read in small chunks and check cancellation between
    chunks, so a long download can be stopped promptly instead of blocking in
    one resp.read() until the full socket timeout (which made "stop" look dead).
    The active response is also published on ctx.rt so the stop handler can
    close it and abort a socket that has stalled mid-read.
    """
    headers = {"User-Agent": WH_UA, "Accept": "application/json, image/*"}
    if api_key:
        headers["X-API-Key"] = api_key
    req = urllib.request.Request(url, headers=headers)
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        if ctx is None:
            return resp.read()
        rt = getattr(ctx, "rt", None)
        if rt is not None:
            with _tasks_lock:
                rt["_resp"] = resp
        try:
            parts = []
            while True:
                if ctx.cancelled():
                    raise _FetchCancelled()
                part = resp.read(65536)
                if not part:
                    break
                parts.append(part)
            return b"".join(parts)
        finally:
            if rt is not None:
                with _tasks_lock:
                    rt.pop("_resp", None)


def wh_search(page, cfg, ctx=None):
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
    raw = wh_request(WH_API + "?" + urlencode(params), cfg["api_key"], ctx=ctx)
    return json.loads(raw.decode("utf-8"))


def wh_fetch_image(item, cfg, ctx=None):
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
    return wh_request(full, cfg["api_key"], timeout=90, ctx=ctx), name, "原图"


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
    note = getattr(ctx, "note", None) or _fetch_note
    setst = getattr(ctx, "set", None) or _fetch_set
    note("采集失败：" + message)
    setst(running=False, finished=time.time(), phase="error", error=message)


# ---- 采集熔断阈值（集中管理，便于按实际网络环境调整）----
_FETCH_GUARDS = {
    "max_dl_fail": 12,          # 连续下载失败（HTTP/业务错误）
    "max_net_err": 6,           # 连续网络异常/超时（含搜索与下载）
    "max_429_streak": 5,        # 连续限流冷却次数
    "max_idle_pages": 6,        # 连续 N 页零新增 → 软/硬结束
    "max_runtime_sec": 60 * 60, # 单任务最长运行 60 分钟
    "max_total_images": 480,    # 单次任务最多采集 480 张（任务 count 上限同步为 480）
    "max_page_span": 100,       # 单次任务翻页跨度：从起始页起最多翻 100 页
    "min_free_mb": 512,         # 磁盘可用空间下限（MB）
}


class _FetchHalt(Exception):
    """采集熔断：由 trip() 抛出，携带原因交给共享 finally 收尾。"""


def _disk_free_mb(path):
    """返回 path 所在盘的可用 MB；不支持时返回 None（Windows 本地跳过检查）。"""
    try:
        st = os.statvfs(path)
        return (st.f_bavail * st.f_frsize) / (1024.0 * 1024.0)
    except (AttributeError, OSError):
        return None


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

    G = _FETCH_GUARDS
    halt = [None]                       # (reason, soft) —— 熔断原因；soft=True 记为正常结束
    def trip(reason, soft=False):
        if halt[0] is None:
            halt[0] = (reason, soft)
            note("自动停止：" + reason)

    setst(target=dest, done=0, total=cfg["count"], page=0, error="")
    rng = "随机起始页"
    if cfg["start_page"]:
        rng = "第 %d 页起" % cfg["start_page"]
    if cfg["end_page"]:
        rng += " 至第 %d 页" % cfg["end_page"]
    note("开始采集 → %s（目标 %d 张，%s，按接口顺序下载）" % (dest, cfg["count"], rng))

    # 磁盘空间不足在进入主循环前就熔断，避免半途写入失败留下残片
    free = _disk_free_mb(dest)
    if free is not None and free < G["min_free_mb"]:
        _fetch_fail("磁盘可用空间不足（剩余 %.0f MB，低于 %d MB 阈值）"
                    % (free, G["min_free_mb"]), ctx)
        return

    try:
        first = wh_search(1, cfg, ctx)
        # API 返回 200 但结构异常（无 data / meta 不是对象）时熔断，避免空转翻页
        if not isinstance(first, dict) or not isinstance(first.get("data"), list):
            trip("API 返回结构异常（缺少 data 列表），请检查接口或 API Key")
            raise _FetchHalt()
        last = int((first.get("meta") or {}).get("last_page") or 1)
    except _FetchCancelled:
        # Stop pressed during the first probe: fall through to the shared
        # finish below so the task is finalised as cancelled, not failed.
        setst(running=False, finished=time.time(), phase="cancelled", error="")
        note("采集已停止")
        return
    except _FetchHalt:
        _fetch_fail(halt[0][0], ctx)
        return
    except urllib.error.HTTPError as exc:
        if exc.code in (401, 403):
            _fetch_fail("API 鉴权失败（HTTP %d），请检查 Wallhaven API Key" % exc.code, ctx)
        else:
            _fetch_fail("访问 wallhaven API 失败：HTTP %d" % exc.code, ctx)
        return
    except Exception as exc:
        # 网络层异常（URLError/timeout）：首次探测即失败，直接报错结束
        _fetch_fail("访问 wallhaven API 失败：%s" % exc, ctx)
        return
    if cfg["end_page"]:
        last = min(last, cfg["end_page"])
    last = max(1, last)
    span = G["max_page_span"]
    # 起始页 0 = 在 1..last 内随机选起点，从那里顺序翻；翻到 last 后回绕到 1
    # 继续翻到起点前一页（即覆盖 1..last 一圈），张数达标即停；最多翻 span 页。
    # 起始页非 0 = 从该页线性顺序翻到 min(last, 起点+span-1)，不回绕。
    wrap = cfg["start_page"] == 0
    first_page = random.randint(1, last) if wrap else cfg["start_page"]
    if first_page > last:
        note("起始页 %d 超出可用范围，改从第 %d 页开始" % (first_page, last))
        first_page = last
    first_page = max(1, first_page)
    if wrap:
        # 环形一圈 = last 页；单次最多翻 span 页，两者取小
        page_cap = min(last, span)
        note("随机起点第 %d 页，在 1-%d 页内环形顺序翻，单次最多翻 %d 页"
             % (first_page, last, page_cap))
    else:
        if last > first_page + span - 1:
            note("单次翻页跨度上限 %d 页，翻页范围缩减到第 %d 页"
                 % (span, first_page + span - 1))
            last = first_page + span - 1
        page_cap = 0                    # 线性模式仍用 next_page <= last 终止
        note("起始第 %d 页，翻页范围 %d-%d（单次最多翻 %d 页）"
             % (first_page, first_page, last, span))

    min_size = cfg["min_size_kb"] * 1024
    max_size = cfg["max_size_mb"] * 1024 * 1024 if cfg["max_size_mb"] else float("inf")
    done = 0
    next_page = first_page
    pages_visited = 0           # 已翻页数（环形模式用于 span 上限与防重复一圈）
    rate_limited = 0
    dl_fail = 0                 # 连续下载失败（业务/HTTP 非鉴权）
    net_err = 0                 # 连续网络异常（timeout / URLError）
    idle_pages = 0              # 连续零新增页数
    skipped_this_page = 0       # 本页因黑名单/已存在被跳过的数量
    page_added = 0              # 本页实际下载数
    started = time.time()

    def advance_page(cur):
        """推进到下一页；环形模式到 last 后回绕到 1，并累计已翻页数。"""
        nonlocal pages_visited
        nxt = cur + 1
        if wrap:
            pages_visited += 1
            if nxt > last:
                nxt = 1
        return nxt

    try:
        while (done < cfg["count"] and not ctx.cancelled()
               and (pages_visited < page_cap if wrap else next_page <= last)):
            # 单次任务总张数硬上限（soft 结束，不算失败）
            if done >= G["max_total_images"]:
                trip("已达单次任务总张数上限 %d 张，自动结束" % G["max_total_images"], soft=True)
                raise _FetchHalt()
            # 总时长上限：防慢速拖拽式网络异常
            if time.time() - started > G["max_runtime_sec"]:
                trip("任务运行超过 %d 分钟，自动停止"
                     % (G["max_runtime_sec"] // 60))
                raise _FetchHalt()
            # 磁盘空间：每页检查一次
            free = _disk_free_mb(dest)
            if free is not None and free < G["min_free_mb"]:
                trip("磁盘可用空间不足（剩余 %.0f MB）" % free)
                raise _FetchHalt()
            # 连续零新增页：区分「黑名单命中过多（软结束）」与「筛选过严（硬停）」
            if idle_pages >= G["max_idle_pages"]:
                if skipped_this_page > 0 or skipped_blacklist[0] > 0:
                    trip("连续 %d 页无新增，黑名单/已存在命中过多，可能已采干净"
                         % idle_pages, soft=True)
                else:
                    trip("连续 %d 页无新增，筛选条件可能过严" % idle_pages)
                raise _FetchHalt()

            page = next_page
            setst(page=page)
            note("抓取第 %d 页…" % page)
            skipped_this_page = 0
            page_added = 0
            try:
                data = wh_search(page, cfg, ctx)
                rate_limited = 0
                net_err = 0                     # 成功一次即清零连续网络异常
            except _FetchCancelled:
                raise                          # let the outer finally finalise
            except _FetchHalt:
                raise
            except urllib.error.HTTPError as exc:
                if exc.code in (401, 403):
                    trip("API 鉴权失败（HTTP %d），请检查 Wallhaven API Key" % exc.code)
                    raise _FetchHalt()
                if exc.code == 429:
                    rate_limited += 1
                    note("触发限流 429，冷却 30 秒（第 %d 次）" % rate_limited)
                    if ctx.wait(30) or rate_limited >= G["max_429_streak"]:
                        if rate_limited >= G["max_429_streak"]:
                            trip("连续 %d 次限流，自动停止" % rate_limited)
                            raise _FetchHalt()
                        break
                    continue                   # keep next_page: retry same page
                # 搜索失败（非鉴权/非限流）：计入网络异常，累计到阈值熔断
                net_err += 1
                note("第 %d 页请求失败 HTTP %s（连续 %d 次）" % (page, exc.code, net_err))
                if net_err >= G["max_net_err"]:
                    trip("连续 %d 次请求异常，网络或接口不稳定" % net_err)
                    raise _FetchHalt()
                next_page = advance_page(page)
                continue
            except Exception as exc:
                net_err += 1
                note("第 %d 页请求失败 %s（连续 %d 次）" % (page, exc, net_err))
                if net_err >= G["max_net_err"]:
                    trip("连续 %d 次请求异常，网络或接口不稳定" % net_err)
                    raise _FetchHalt()
                next_page = advance_page(page)
                continue
            next_page = advance_page(page)

            # Keep the API's order: "start at page 5" means page 5's first
            # image first. Previously random.shuffle() broke this guarantee.
            items = list(data.get("data") or [])
            if not items:
                idle_pages += 1
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
                    skipped_this_page += 1
                    continue

                tmp = ""
                try:
                    # 第一段：网络下载（只这里抛网络异常）
                    try:
                        blob, name, label = wh_fetch_image(it, cfg, ctx)
                    except _FetchCancelled:
                        raise
                    except urllib.error.HTTPError as exc:
                        if exc.code in (401, 403):
                            trip("API 鉴权失败（HTTP %d），请检查 Wallhaven API Key" % exc.code)
                            raise _FetchHalt()
                        if exc.code == 429 and not ctx.wait(30):
                            note("下载遇到 429，已等待 30 秒")
                        raise                    # 交给外层按下载失败计数
                    except (urllib.error.URLError, TimeoutError, socket.timeout) as exc:
                        net_err += 1
                        note("网络异常 %s（连续 %d 次）：%s" % (wid, net_err, exc))
                        if net_err >= G["max_net_err"]:
                            trip("连续 %d 次网络异常，自动停止" % net_err)
                            raise _FetchHalt()
                        dl_fail += 1
                        if dl_fail >= G["max_dl_fail"]:
                            trip("连续 %d 次下载失败，自动停止" % dl_fail)
                            raise _FetchHalt()
                        continue
                    net_err = 0                 # 下载成功即清零网络异常

                    # Only originals are downloaded now; guard against a
                    # truncated/placeholder response slipping into the library.
                    if len(blob) > max_size or len(blob) < 2048:
                        note("跳过 %s（实际 %d 字节不符）" % (name, len(blob)))
                        continue
                    if os.path.exists(os.path.join(dest, name)):
                        seen.add(wid)
                        skipped_this_page += 1
                        continue

                    # 第二段：非网络写入失败（磁盘满/权限）→ 立即熔断
                    tmp = os.path.join(dest, "." + name + ".part")
                    try:
                        with open(tmp, "wb") as fh:
                            fh.write(blob)
                        os.replace(tmp, os.path.join(dest, name))
                    except OSError as exc:
                        trip("写入图片失败（磁盘/权限）：%s" % exc)
                        raise _FetchHalt()
                    dl_fail = 0                 # 成功落盘即清零连续失败
                except _FetchCancelled:
                    raise                      # let the outer finally finalise
                except _FetchHalt:
                    raise
                except urllib.error.HTTPError as exc:
                    note("下载失败 %s：HTTP %s" % (wid, exc.code))
                    dl_fail += 1
                    if dl_fail >= G["max_dl_fail"]:
                        trip("连续 %d 次下载失败，自动停止" % dl_fail)
                        raise _FetchHalt()
                    continue
                except Exception as exc:
                    dl_fail += 1
                    note("下载失败 %s：%s（连续 %d 次）" % (wid, exc, dl_fail))
                    if dl_fail >= G["max_dl_fail"]:
                        trip("连续 %d 次下载失败，自动停止" % dl_fail)
                        raise _FetchHalt()
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
                page_added += 1
                setst(done=done)
                note("已下载 %d/%d：%s（%s，%d KB，收藏 %s）"
                            % (done, cfg["count"], name, label, len(blob) // 1024, fav))
            # 本页零新增：累计连续页数
            if page_added == 0:
                idle_pages += 1
            else:
                idle_pages = 0
    except _FetchHalt:
        pass                                # halt 已记录原因，统一在 finally 收尾
    except Exception as exc:
        # 未预期的写入/IO 异常（非网络）：作为硬失败，不当成普通下载跳过
        trip("采集过程异常：%s" % exc)
    finally:
        _cache["ts"] = 0.0
        cancelled = ctx.cancelled()
        reason, soft = halt[0] if halt[0] else ("", False)
        if cancelled:
            phase, err = "cancelled", ""
        elif reason:
            phase = "done" if soft else "error"
            err = "" if soft else reason
        else:
            phase = "done"
            err = "" if done else "没有找到符合条件的图片，可放宽筛选条件"
        setst(running=False, finished=time.time(), phase=phase, error=err)
        extra = ("；黑名单跳过 %d 张" % skipped_blacklist[0]) if skipped_blacklist[0] else ""
        tail = ("（%s）" % reason) if reason else ""
        note("采集结束，共 %d 张%s%s；接口列表已刷新" % (done, extra, tail))


def _run_tool(argv, timeout=180, ctx=None):
    """Run an image tool; return (ok, stdout). Raises _FetchCancelled on stop.

    The live Popen handle is exposed on ctx.rt['_proc'] so the stop endpoint
    can terminate it immediately instead of waiting out the subprocess timeout.
    """
    rt = getattr(ctx, "rt", None) if ctx is not None else None
    try:
        p = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except OSError as exc:
        return False, str(exc)
    if rt is not None:
        with _tasks_lock:
            rt["_proc"] = p
    try:
        try:
            out, _err = p.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            try:
                p.kill()
            except Exception:
                pass
            try:
                out, _err = p.communicate()
            except Exception:
                out, _err = b"", b""
            if ctx is not None and ctx.cancelled():
                raise _FetchCancelled()
            return False, "timeout"
    finally:
        if rt is not None:
            with _tasks_lock:
                if rt.get("_proc") is p:
                    rt.pop("_proc", None)
    if ctx is not None and ctx.cancelled():
        raise _FetchCancelled()
    return p.returncode == 0, (out or b"").decode("utf-8", "replace").strip()


def _img_dims(ffprobe, path, ctx=None):
    """Return (width, height) via ffprobe; (0, 0) when unreadable."""
    ok, out = _run_tool([ffprobe, "-v", "error", "-select_streams", "v:0",
                         "-show_entries", "stream=width,height",
                         "-of", "csv=p=0", path], timeout=30, ctx=ctx)
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

    # 主文件名（不含扩展名）集合：备份目录里已有的同名图片不再重复备份。
    # 文件名相同但格式不同（a.jpg / a.png）视为同名。
    backed_stems = set()
    # 本次真正落到备份目录的采集图 ID，任务收尾时登记进备份目录自己的
    # downloaded.txt（该文件 = 所在文件夹的图片索引）。
    backed_wids = set()
    try:
        with os.scandir(backup) as bit:
            for be in bit:
                if be.is_file():
                    backed_stems.add(os.path.splitext(be.name)[0])
    except OSError:
        pass

    def _backup_original(path, name):
        """备份原图；备份目录已有同名（忽略格式）则跳过。返回是否可用。

        采集图（wallhaven-<id>）落盘后同步把 ID 记入 backed_wids，收尾时
        写进备份目录的 downloaded.txt，让「每个文件夹的索引=现存图片」成立。
        自传图取不到 wid，不写索引。
        """
        stem = os.path.splitext(name)[0]
        wid = image_wid(name)
        if stem in backed_stems:
            if wid:
                backed_wids.add(wid)
            return True
        bpath = os.path.join(backup, name)
        if os.path.exists(bpath):
            backed_stems.add(stem)
            if wid:
                backed_wids.add(wid)
            return True
        try:
            shutil.copy2(path, bpath)
            backed_stems.add(stem)
            if wid:
                backed_wids.add(wid)
            return True
        except OSError as exc:
            note("备份失败，跳过：%s（%s）" % (name, exc))
            return False

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

    # 全量备份：备份源目录所有图片（含未 Compression 候选的格式），跳过同名。
    backed = 0
    if cfg.get("full_backup"):
        allimgs = []
        try:
            if cfg["recursive"]:
                for root, _dirs, names in os.walk(src):
                    if os.path.abspath(root).startswith(os.path.abspath(tmpdir)):
                        continue
                    for n in names:
                        if os.path.splitext(n)[1].lower() in SUPPORTED:
                            allimgs.append(os.path.join(root, n))
            else:
                with os.scandir(src) as it:
                    for e in it:
                        if e.is_file() and os.path.splitext(e.name)[1].lower() in SUPPORTED:
                            allimgs.append(e.path)
        except OSError as exc:
            _fetch_fail("全量备份扫描失败：%s" % exc, ctx)
            return
        allimgs.sort()
        for p in allimgs:
            if ctx.cancelled():
                break
            before = len(backed_stems)
            if _backup_original(p, os.path.basename(p)) and len(backed_stems) > before:
                backed += 1
        note("全量备份：已备份 %d 张（共 %d 张，同名或失败跳过 %d 张）"
             % (backed, len(allimgs), len(allimgs) - backed))

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

            width, height = _img_dims(ffprobe, path, ctx)
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

            # 1) backup original (once, keeps original format & full detail;
            #    skip if a same-name image already exists in backup dir)
            if not _backup_original(path, name):
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
                return _run_tool(argv, timeout=180, ctx=ctx)

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
                    if ctx.cancelled():
                        raise _FetchCancelled()
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
            nw, nh = _img_dims(ffprobe, final, ctx)
            note("完成：%s → %dx%d，%dKB（原 %dKB）" %
                 (os.path.basename(final), nw, nh, new_kb, size_kb))
    finally:
        # 备份目录的 downloaded.txt = 该文件夹的图片索引：把本次落盘的采集图
        # ID 登记进去（含取消时已备份的部分），保证「有图必有记录」。
        if backed_wids:
            n = add_downloaded_records(backup, backed_wids)
            if n:
                note("备份索引：新增 %d 条下载记录（备份目录 %s）"
                     % (n, os.path.basename(backup)))
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


def any_task_running():
    """是否有采集/压缩任务正在运行。

    魔术师补拉黑会强制重扫并把「downloaded.txt 有记录但当前无文件」的 ID
    拉黑；采集任务若处于「已清空目标目录、新图尚未下完」的窗口，整批 ID 会
    被误判成外部删除。故魔术师执行前先避开任务运行期。
    """
    with _tasks_lock:
        return any(bool(rt.get("running")) for rt in _task_rt.values())


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
                    "last_scheduled_run": str(it.get("last_scheduled_run") or ""),
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
        "last_run": t["last_run"], "last_scheduled_run": t.get("last_scheduled_run", ""),
        "last_status": t["last_status"],
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


def run_task_job(tid, scheduled=False):
    """Execute one task in the single worker thread.

    scheduled=True 表示由定时调度器入队，完成时写 last_scheduled_run；
    手动点「立即运行」不写，避免占用当天的定时额度。
    """
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
    ctx.note("开始执行任务：%s（%s，%s）" % (t["name"], t["time"], "定时" if scheduled else "手动"))
    try:
        if kind == "compress":
            compress_images(dict(cfg), ctx)
            _cache["ts"] = 0.0            # compressed files changed -> refresh APIs
        else:
            # 采集前补拉黑：把「downloaded.txt 有记录但文件已不在」的 ID 写入全局黑名单，
            # 防止换分类采集时把外部删掉的图重新下载回来。任务在单线程 worker 串行执行，
            # 且此处早于 wh_collect 的清空目录逻辑，不会把正在下载的图误判为已删除。
            try:
                sok, sw = sweep_missing_blacklist()
                if sok and sw.get("added"):
                    ctx.note("采集前补拉黑：新拉黑 %d 个 ID（黑名单共 %d），清理失效记录 %d 条"
                             % (sw["added"], sw["total"], sw.get("records_removed", 0)))
                elif not sok:
                    ctx.note("采集前补拉黑失败：%s" % sw)
            except Exception as exc:
                log("pre-fetch blacklist sweep failed: %s" % exc)
            run_cfg = apply_global_key(dict(cfg))
            if not run_cfg["api_key"] and run_cfg["purity"] != "100":
                ctx.note("未填写 API Key，按规则强制仅下载 SFW")
            wh_collect(run_cfg, ctx)
    except _FetchCancelled:
        # wh_collect's finally already finalised the stop; keep the cancelled
        # phase instead of letting the generic handler below turn it into error.
        pass
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
            if scheduled:
                t["last_scheduled_run"] = t["last_run"]
            t["last_status"] = status
            t["last_count"] = rt["done"]
            if not t.get("days"):
                t["enabled"] = False          # one-shot: auto-disable after first run
            rt["running"] = False
        _cache["ts"] = 0.0
        save_tasks()


def _task_worker():
    while True:
        item = _task_queue.get()
        try:
            if isinstance(item, tuple):
                tid, scheduled = item[0], bool(item[1])
            else:
                tid, scheduled = item, False
            run_task_job(tid, scheduled)
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
                    if t.get("last_scheduled_run", "").startswith(today):
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
                _task_queue.put((tid, True))
                log("scheduler: queued task %s" % tid)
        except Exception as exc:
            log("scheduler error: %s" % exc)


def start_tasks():
    load_tasks()
    threading.Thread(target=_task_worker, daemon=True).start()
    threading.Thread(target=_scheduler_loop, daemon=True).start()



PAGE = Template("""<!doctype html><html lang="zh-CN" data-theme="$theme"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1,user-scalable=no,viewport-fit=cover">
<link rel="icon" type="image/png" href="$base/_icon">
<title>$title · 随机图片 API</title>
<script>(function(){var h=document.documentElement,p=h.getAttribute('data-theme')||'auto',
m=window.matchMedia&&window.matchMedia('(prefers-color-scheme: dark)');
/* 主题按设备独立：本机选择存 localStorage，不写服务端配置，手机/电脑互不同步 */
try{var s=localStorage.getItem('ranpix_theme');if(s==='auto'||s==='light'||s==='dark')p=s;}catch(e){}
h.setAttribute('data-theme',p);
function ap(){var d=p==='dark'||(p==='auto'&&m&&m.matches);if(d)h.classList.add('theme-dark');else h.classList.remove('theme-dark');}
ap();window.rpTheme=function(v){p=v;h.setAttribute('data-theme',v);try{localStorage.setItem('ranpix_theme',v)}catch(e){};ap();};
if(m){var f=function(){if((h.getAttribute('data-theme')||'auto')==='auto')ap();};
if(m.addEventListener)m.addEventListener('change',f);else if(m.addListener)m.addListener(f);}})();</script>
<style>
:root{color-scheme:light;
--brand:#4a63d8;--ink:#1f2328;--muted:#656d76;--line:#e3e6ea;
--c-run:#2f7de1;--c-set:#0f9b8e;--c-api:#7a5af0;--c-wall:#e0703a;--c-zip:#2f9e66;--c-help:#8a94a3}
*{box-sizing:border-box;-webkit-user-select:none;user-select:none;-webkit-touch-callout:none}
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
/* 使用说明常驻展开（无折叠）；标题固定在卡片顶部，内容在 help-body 内滚动 */
.help-summary{font-size:15px;font-weight:600;
display:flex;align-items:center;gap:8px;min-height:24px;
background:#fff;padding:26px 20px 14px 22px;margin:0;border-bottom:1px solid var(--line)}
.help-summary::after{content:"";width:7px;height:15px;border-radius:3px;background:var(--accent,#c9d0da);order:-1}
/* helpbox 撑满卡片；标题固定，正文 help-body 作为直接 flex 子项才能收缩滚动 */
#helpbox{display:flex;flex-direction:column;flex:0 1 auto;height:auto;max-height:100%;min-height:0}
.help-body{flex:0 1 auto;min-height:0;overflow-y:auto;overflow-x:hidden;overscroll-behavior:contain;
 padding:16px 20px 20px 22px;scrollbar-gutter:stable}
code{background:#f1f3f5;padding:2px 6px;border-radius:5px;font-size:12.5px;
word-break:break-all;overflow-wrap:anywhere}
a{color:#185fa5;text-decoration:none;overflow-wrap:anywhere}
/* 16px 是关键：iOS/WebView 聚焦小于 16px 的输入框会自动放大页面 */
input,select,textarea{border:1px solid #d5d9de;border-radius:6px;
padding:7px 10px;font:inherit;font-size:16px;width:100%;min-width:0;
background:#fff;color:#1f2328;-webkit-appearance:none;appearance:none;
-webkit-user-select:text;user-select:text;-webkit-touch-callout:default}
label{display:block;font-size:13px;color:#656d76;margin-bottom:5px}
.grid{display:flex;flex-wrap:wrap;gap:12px;align-items:flex-end}
/* 主题下拉展开撑高本行时，同排设置项保持顶部对齐，不被一起推下去 */
.grid.theme-grid{align-items:flex-start}
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
.cpbox{flex:1 1 100%;-webkit-user-select:text;user-select:text;-webkit-touch-callout:default}
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
#msg:empty{display:none}
.cfgmsg{display:none;margin-top:10px;padding:9px 12px;border-radius:8px;font-size:13px;line-height:1.5;overflow-wrap:anywhere}
.cfgmsg.show{display:block}
#checkmsg{white-space:pre-line}
.chkicon{display:inline-flex;width:17px;height:17px;flex:none;align-items:center;justify-content:center;
border-radius:3px;cursor:pointer;vertical-align:middle;margin-left:6px}
.chkicon svg{stroke:currentColor;fill:none;stroke-width:2;stroke-linecap:round;stroke-linejoin:round}
.chkicon svg circle{fill:currentColor}
.chkicon:hover{background:rgba(127,127,127,.12)}
#consistency.c-ok{color:#1a7f37}
#consistency.c-bad{color:#b42318}
html.theme-dark #consistency.c-ok{color:#3fb950}
html.theme-dark #consistency.c-bad{color:#f85149}
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
/* 设置页开关：保留原生 checkbox 语义，视觉做成滑动开关 */
.cleanup-row{padding:12px 14px;border:1px solid var(--line);border-radius:12px;background:#fff}
.cleanup-row label{display:inline-flex;align-items:center;gap:8px;margin-bottom:0;
font-size:15px;font-weight:600;color:#1f2328;cursor:pointer}
.cleanup-row .kv{display:block;margin-top:5px}
.cleanup-row input[type=checkbox]{-webkit-appearance:none;appearance:none;
position:relative;width:42px;height:24px;flex:none;min-width:0;margin:0;padding:0;
border:2px solid #6e7580;border-radius:12px;background:#eef0f3;
cursor:pointer;vertical-align:middle;transition:background .15s,border-color .15s}
.cleanup-row input[type=checkbox]::before{content:"";position:absolute;top:2px;left:3px;
width:16px;height:16px;border-radius:50%;background:#6e7580;
transition:transform .15s,background .15s}
.cleanup-row input[type=checkbox]:checked{background:#4a63d8;border-color:#4a63d8}
.cleanup-row input[type=checkbox]:checked::before{transform:translateX(14px);background:#fff}
.cleanup-row input[type=checkbox]:disabled{opacity:.4;cursor:not-allowed}
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
.apikeybox input::placeholder{font-size:12px}
.apikeybox input::-webkit-input-placeholder{font-size:12px}
#keysave{display:inline-flex;align-items:center;gap:6px}
#keysave svg{width:14px;height:14px;stroke:currentColor;fill:none;stroke-width:1.8;
  stroke-linecap:round;stroke-linejoin:round}
.keydot{display:inline-block;width:8px;height:8px;border-radius:50%;margin-left:6px;
  vertical-align:middle;background:#b42318}
.keydot.on{background:#1a7f37}
.badge.on{background:#eefbf3;color:#1a7f37}
.badge.off{background:#fff1f0;color:#b42318}
/* select 已并入上方 input,select,textarea 规则（16px 防聚焦放大），此处保留下拉箭头 */
select{-webkit-appearance:none;appearance:none;
background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='10' height='6'%3E%3Cpath d='M1 1l4 4 4-4' stroke='%23656d76' fill='none'/%3E%3C/svg%3E");
background-repeat:no-repeat;background-position:right 10px center;padding-right:28px}
/* 主题模式：标题与下拉同一行，字体与“清理自传图副本”一致 */
.theme-row{display:flex;align-items:flex-start;gap:12px;margin-top:14px}
.theme-row label{flex:none;font-size:15px;font-weight:600;color:#1f2328;
  margin-bottom:0;white-space:nowrap;padding-top:11px}
.theme-row .tset{flex:0 1 210px;width:210px;min-width:0}
/* 主题模式下拉：三个圆角矩形选项 */
.tset{width:100%}
.tcur{position:relative;border:1px solid #d5d9de;border-radius:6px;padding:7px 28px 7px 10px;
background:#fff;color:#1f2328;font-size:16px;line-height:1.6;cursor:pointer}
.tcur::after{content:"";position:absolute;right:12px;top:50%;width:7px;height:7px;
border-right:1.8px solid #656d76;border-bottom:1.8px solid #656d76;
transform:translateY(-70%) rotate(45deg);pointer-events:none}
/* 普通文档流：展开时把下方内容顺延，不遮挡按钮；同排项由 .theme-grid 顶部对齐兜底 */
.topts{display:none;margin-top:4px;padding:0;background:#f5f7fa;
border:1px solid var(--line);border-radius:10px;overflow:hidden}
.tset.open .topts{display:block}
.topt{border-radius:9px;padding:7px 9px;cursor:pointer;font-size:15px;color:var(--ink)}
.topt:hover,.topt.on{background:#e4ebfa;color:#2a4a9a;border-radius:0}
/* In-page preview: a new window is blocked by the fnOS App WebView, so show
   the image in a lightbox inside this iframe instead. */
#pv{position:fixed;top:0;left:0;right:0;bottom:0;inset:0;z-index:9999;
display:flex;align-items:center;justify-content:center;padding:14px;
background:rgba(20,24,30,.74)}
#pv .card{position:relative;background:#fff;border-radius:12px;width:100%;max-width:728px;
max-height:100%;display:flex;flex-direction:column;overflow:hidden;padding:0;
margin:0;border:0}
#pv .bar{display:flex;align-items:center;justify-content:space-between;gap:10px;
padding:10px 14px;border-bottom:1px solid rgba(0,0,0,.06);font-size:14px;min-width:0;
position:absolute;top:0;left:0;right:0;z-index:4;
background:rgba(255,255,255,.30);-webkit-backdrop-filter:blur(10px);backdrop-filter:blur(10px)}
#pv .bar span{flex:1 1 auto;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
#pv .bar button{display:inline-flex;align-items:center;justify-content:center;flex:none;padding:0;width:30px;height:30px}
#pv .bar button svg{width:16px;height:16px;stroke:currentColor;fill:none;stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round}
#pv .body{flex:1 1 auto;min-height:140px;display:flex;align-items:center;
justify-content:center;padding:0;background:#f5f7fa;overflow:auto;position:relative}
#pv .frame{position:relative;display:block;width:100%;max-width:100%;line-height:0;overflow:hidden}
#pv img{display:block;width:calc(100% + 2px);max-width:none;height:auto;margin-left:-1px;object-fit:contain;touch-action:pan-y}
/* 图片角标：最近下载左上、关闭右上、图片ID左下、x/xx 右下；挂在 bwrap（滚动容器之外），滚动时静止 */
#pv .bwrap #pvTitle,#pv .bwrap #pvId,#pv .bwrap #pvIdx{position:absolute;z-index:2;line-height:1;
padding:4px 8px;border-radius:10px;font-size:13px;font-weight:400;
background:rgba(255,255,255,.45);color:#fff;pointer-events:none;user-select:none;
-webkit-backdrop-filter:blur(10px);backdrop-filter:blur(10px)}
#pv .bwrap #pvTitle{top:8px;left:8px}
#pv .bwrap #pvId{bottom:8px;left:8px}
#pv .bwrap #pvIdx{bottom:8px;right:8px}
/* 关闭按钮：右上角角标 */
#pv .bwrap #pvX{position:absolute;right:8px;top:8px;z-index:5;
display:inline-flex;align-items:center;justify-content:center;padding:0;
width:30px;height:30px;border:0;border-radius:50%;
background:rgba(255,255,255,.45);color:#fff;cursor:pointer;
-webkit-backdrop-filter:blur(10px);backdrop-filter:blur(10px)}
#pv .bwrap #pvX svg{width:16px;height:16px;stroke:currentColor;fill:none;stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round}
/* 深色模式：角标回深色底白字 */
html.theme-dark #pv .bwrap #pvTitle,html.theme-dark #pv .bwrap #pvId,html.theme-dark #pv .bwrap #pvIdx,
html.theme-dark #pv .bwrap #pvX{background:rgba(20,24,30,.45);color:#fff}
#pv .pvn{display:none;position:absolute;top:50%;transform:translateY(-50%);z-index:3;
width:44px;height:44px;padding:0;align-items:center;justify-content:center;border-radius:50%;
background:rgba(255,255,255,.45);border:0;color:#fff;cursor:pointer;
-webkit-backdrop-filter:blur(10px);backdrop-filter:blur(10px)}
#pv .pvn:hover{background:rgba(255,255,255,.72)}
#pv .pvn svg{width:24px;height:24px;stroke:currentColor;fill:none;stroke-width:2;stroke-linecap:round;stroke-linejoin:round}
#pv .pvn.prev{left:14px}
#pv .pvn.next{right:14px}
@media(min-width:901px){#pv .pvn{display:inline-flex}}
#pv .err{color:#b42318;font-size:13px;overflow-wrap:anywhere;padding:8px}
#pv .foot{display:flex;flex-wrap:wrap;align-items:center;justify-content:center;gap:28px;
padding:10px 14px;border-top:1px solid rgba(0,0,0,.06);
position:absolute;bottom:0;left:0;right:0;z-index:4;
background:rgba(255,255,255,.30);-webkit-backdrop-filter:blur(10px);backdrop-filter:blur(10px)}
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
/* 全屏看图：铺满整个 WebView/iframe，不依赖浏览器 Fullscreen API（iframe 内常被拦截） */
#pv.full{padding:0;background:#f5f7fa}
#pv.full .card{max-width:none;width:100%;height:100%;max-height:none;border:0;border-radius:0}
#pv.full .bar{position:absolute;top:0;left:0;right:0;z-index:4;
background:rgba(255,255,255,.30);border-bottom-color:rgba(0,0,0,.06)}
#pv.full .bar span{color:var(--ink)}
#pv.full .body{background:#f5f7fa;padding:0}
#pv.full .frame{display:inline-block;width:auto;max-width:100%;overflow:visible}
#pv.full img{width:auto;height:auto;max-width:100vw;max-height:100vh;margin-left:0}
#pv.full .foot{position:absolute;bottom:0;left:0;right:0;z-index:4;
background:rgba(255,255,255,.30);border-top-color:rgba(0,0,0,.06)}
@media(max-width:900px){
 .layout{flex-direction:column;align-items:stretch;height:100vh;height:100dvh;margin:0;padding:12px;gap:12px}
 .side{width:100%;flex:none;height:auto;max-height:none;overflow:visible;position:static;padding:12px}
 /* 关键：锁定主区宽度=视口减去 padding，避免被卡片内长文本 min-content 撑破屏幕 */
 /* 高度改用 flex 传递（不再依赖 height:auto + 百分比）：让 panel 撑满主区，
    卡片 max-height:100% 与正文 .help-body/.card-body 的滚动才能生效 */
 .main{flex:1;min-height:0;height:auto;width:100%;min-width:0;display:flex;flex-direction:column}
 .panel.on{flex:1;min-height:0;height:auto}
 .brand{padding-bottom:10px;margin-bottom:6px}
 .nav{flex-direction:row;overflow-x:auto;-webkit-overflow-scrolling:touch;gap:4px;padding-bottom:3px}
 .nav a{flex:0 0 auto;padding:9px 13px;font-size:13.5px}
 /* 手机端竖屏看图：以图片区高度铺满为基准等比缩放（长图一屏看全，宽度自适应不裁切）；旋转态另有规则 */
 #pv.full:not(.rot90):not(.rot270):not(.rot180) .frame{display:flex;align-items:center;justify-content:center;
  width:100%;height:100%;max-width:none;max-height:none}
 #pv.full:not(.rot90):not(.rot270):not(.rot180) img{width:auto;height:auto;
  max-width:100%;max-height:100%;margin-left:0;object-fit:contain}
}
@media(max-width:640px){
 .wrap{margin:16px auto 40px;padding:0 12px}
 .card-body,.help-body{padding:12px 14px 16px}
 h1{font-size:19px}
 .grid>div,.grid>div.sm,.grid>div.grow{flex:1 1 100%}
 .grid>.btnrow{flex:1 1 100%!important;min-width:0!important;gap:6px}
 .grid>.btnrow button{flex:1 1 0;min-width:0;padding-left:5px;padding-right:5px}
 .grid>.btnrow .chkicon{margin-left:3px}
 .cleanup-row label{display:flex;justify-content:space-between;align-items:center;width:100%}
 .cleanup-row .kv{text-align:right}
 .theme-row{gap:8px}
 .theme-row .tset{flex:0 1 160px;width:160px;margin-left:auto}
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
 .apikeybox .frow{flex-wrap:nowrap}
 .apikeybox .frow input{flex:1 1 auto;min-width:0;margin-left:-5px}
 #keysave{flex:none;margin-right:-5px}
 .api .acts{gap:6px}
 .api .acts button{padding:6px 9px;font-size:13px}
 .api .acts a{font-size:13px}
 /* 预览弹层：全屏/关闭紧挨右上、底部按钮居中；全屏高度用 dvh 避开手机地址栏 */
 #pv .bar span{flex:1 1 auto}
 #pvFull{transform:translateX(-2px)}
 #pv .foot{justify-content:center}
 #pv.full{--pvBot:81px}
 #pv.full .foot{height:var(--pvBot);padding-bottom:40px}
 #pv.full .body{position:absolute;top:0;bottom:var(--pvBot);left:0;right:0;padding:0}
 #pv.full img{width:auto;height:auto;max-width:100vw;max-height:100dvh;margin-left:0}
}
/* 深色模式：由设置中的主题模式控制（auto 跟随系统 / light / dark） */
html.theme-dark{color-scheme:dark;
 --brand:#6a83f0;--ink:#e6edf3;--muted:#8b949e;--line:#30363d;
 --c-run:#4a9bff;--c-set:#2ec4b6;--c-api:#9b83ff;--c-wall:#f0904a;--c-zip:#4fc08d;--c-help:#9aa4b2}
html.theme-dark body{background:#0d1117}
html.theme-dark .side,html.theme-dark .card,html.theme-dark .card h2,html.theme-dark .help-summary,html.theme-dark #tformbox,html.theme-dark #zformbox,
html.theme-dark .sched .clrbox,html.theme-dark #day_box label span,html.theme-dark #z_day_box label span,html.theme-dark #pv .card,html.theme-dark #pv .cfm .cfmcard{background:#161b22}
html.theme-dark .side,html.theme-dark .card{box-shadow:none}
html.theme-dark .brand b,html.theme-dark .opts label,html.theme-dark #pv .cfm .cfmt,html.theme-dark #pv .cfm .cfmk{color:var(--ink)}
html.theme-dark .nav a{color:#8b949e}
html.theme-dark .nav a:hover{background:#21262d;color:var(--ink)}
html.theme-dark .nav a.on{background:#1f2a4a;color:var(--brand)}
html.theme-dark .head{background:linear-gradient(120deg,#2f3f7a,#3a4a8f)}
html.theme-dark code{background:#21262d}
html.theme-dark a{color:#6a9fd8}
html.theme-dark input,html.theme-dark select,html.theme-dark textarea{background:#0d1117;border-color:#30363d;color:var(--ink)}
html.theme-dark label,html.theme-dark .meta,html.theme-dark .kv,html.theme-dark .fstatus,html.theme-dark .api .num,html.theme-dark #pv .foot .u{color:var(--muted)}
html.theme-dark .stat,html.theme-dark .api,html.theme-dark .flog,html.theme-dark .badge,html.theme-dark .fbar{background:#1c2128;border-color:#30363d}
html.theme-dark .api:hover{background:#222831}
html.theme-dark .flog,html.theme-dark .badge{color:#b1bac4}
html.theme-dark button{background:#21262d;border-color:#3a4149;color:var(--ink)}
html.theme-dark button:hover{border-color:#5a6470}
html.theme-dark button.primary{background:#4a63d8;border-color:#4a63d8;color:#fff}
html.theme-dark button.danger,html.theme-dark .cfgmsg.warn{background:#331a1a;border-color:#6e3b36;color:#ff8a80}
html.theme-dark button.danger:hover{background:#432222;border-color:#8a4a44}
html.theme-dark .badge.on,html.theme-dark .cfgmsg.ok{background:#12301f;border-color:#2a6e48;color:#5ddb92}
html.theme-dark .badge.off{background:#331a1a;color:#ff8a80}
html.theme-dark .ok{color:#5ddb92}
html.theme-dark .warn{color:#ff8a80}
html.theme-dark .sec{color:#e0b070;background:#2d2418}
html.theme-dark #zformbox .sec{color:#7ee0ac;background:#143026}
html.theme-dark .opts input[type=checkbox]{border-color:#4a525c;background-color:#0d1117}
html.theme-dark .opts label.off{color:#6e7681}
html.theme-dark .cleanup-row{background:#161b22;border-color:var(--line)}
html.theme-dark .cleanup-row label{color:var(--ink)}
html.theme-dark .theme-row label{color:var(--ink)}
html.theme-dark .cleanup-row input[type=checkbox]{background:#30363d;border-color:#9aa4b2}
html.theme-dark .cleanup-row input[type=checkbox]::before{background:#9aa4b2}
html.theme-dark .cleanup-row input[type=checkbox]:checked{background:#4a63d8;border-color:#4a63d8}
html.theme-dark .cleanup-row input[type=checkbox]:checked::before{background:#fff}
html.theme-dark .keydot{background:#ff8a80}
html.theme-dark .keydot.on{background:#5ddb92}
html.theme-dark #day_box label span,html.theme-dark #z_day_box label span{color:#b1bac4}
html.theme-dark #tformbox{border-color:#4a3a2a}
html.theme-dark #zformbox{border-color:#2a4a38}
html.theme-dark .apikeybox{border-color:#4a3a2a;background:#241c14}
html.theme-dark .tcur{background:#0d1117;border-color:#30363d;color:var(--ink)}
html.theme-dark .tcur::after{border-color:#8b949e}
html.theme-dark .topts{background:#161b22;border-color:#30363d}
html.theme-dark .topt:hover,html.theme-dark .topt.on{background:#1f2a4a;color:var(--brand);border-radius:0}
html.theme-dark #pv{background:rgba(0,0,0,.78)}
html.theme-dark #pv .bar{background:rgba(34,40,49,.30);border-bottom-color:rgba(255,255,255,.10)}
html.theme-dark #pv .card{background:#222831;border:1px solid #3a4149;box-shadow:0 12px 40px rgba(0,0,0,.5)}
html.theme-dark #pv .body{background:#0d1117}
html.theme-dark #pv .foot{background:rgba(34,40,49,.30);border-top-color:rgba(255,255,255,.10)}
html.theme-dark #pv .pvn{background:rgba(20,24,30,.45);color:#fff}
html.theme-dark #pv .pvn:hover{background:rgba(20,24,30,.72)}
html.theme-dark #pv.full{background:#000}
html.theme-dark #pv.full .card{background:#000;border:0;box-shadow:none}
html.theme-dark #pv.full .bar{background:rgba(20,24,30,.30);border-bottom-color:rgba(255,255,255,.14)}
html.theme-dark #pv.full .bar span{color:#fff}
html.theme-dark #pv.full .body{background:#000}
html.theme-dark #pv.full .foot{background:rgba(20,24,30,.30);border-top-color:rgba(255,255,255,.14)}
/* 预览栏按钮：透明底 + 圆角边框（覆盖浅色/深色/危险按钮及其 hover 背景） */
#pv .bar button,#pv .foot button,#pv .bar button:hover,#pv .foot button:hover{background:transparent}
/* 预览栏按钮与标题统一 #282828；删除按钮 #bc0404 */
#pv .bar button,#pv .foot button,#pv .bar button:hover,#pv .foot button:hover{border-color:#282828;color:#282828}
#pv .bar #pvTitle,html.theme-dark #pv.full .bar #pvTitle{color:#282828}
#pv .foot #pvDel,#pv .foot #pvDel:hover{border-color:#bc0404;color:#bc0404}
/* 底栏图标按钮：旋转/全屏，方形紧凑 */
/* 电脑窗口预览：底栏图标圆形边框；底栏自身补下圆角（fnOS WebView 对父级 overflow+圆角裁剪不稳） */
#pv:not(.full) .foot{border-radius:0 0 12px 12px}
#pv:not(.full) .foot button{border-radius:999px}
#pv .foot #pvMagic,#pv .foot #pvDel,#pv .foot #pvRotCcw,#pv .foot #pvRot,#pv .foot #pvFull{display:inline-flex;align-items:center;justify-content:center;flex:none;padding:0;width:30px;height:30px}
#pv .foot #pvMagic svg,#pv .foot #pvDel svg,#pv .foot #pvRotCcw svg,#pv .foot #pvRot svg,#pv .foot #pvFull svg{width:16px;height:16px;stroke:currentColor;fill:none;stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round}
/* 旋转按钮：电脑端与手机端底栏都显示（沿用底栏图标按钮规则，此处不再隐藏） */
/* 长图滚动条：隐藏原生滚动条，改用悬浮在图片上的半透明自定义滑块 */
#pv .bwrap{position:relative;flex:1 1 auto;min-height:0;display:flex}
#pv .body{flex:1 1 auto;overflow:auto;scrollbar-width:none;-ms-overflow-style:none}
#pv .body::-webkit-scrollbar{display:none;width:0;height:0}
#pv .pvscroll{position:absolute;top:0;right:1px;bottom:0;width:3px;z-index:3;
pointer-events:none;background:transparent}
#pv .pvscroll i{position:absolute;right:0;width:3px;min-height:24px;border-radius:6px;
background:rgba(0,0,0,.3);-webkit-backdrop-filter:blur(10px);backdrop-filter:blur(10px)}
/* 全屏预览复用同一套配色与滚动条样式（显式提高优先级覆盖 #pv.full 内部规则） */
#pv.full .bar button,#pv.full .foot button,#pv.full .bar button:hover,#pv.full .foot button:hover{background:transparent;border-color:#282828;color:#282828}
#pv.full .bar #pvTitle,html.theme-dark #pv.full .bar #pvTitle{color:#282828}
#pv.full .foot #pvDel,#pv.full .foot #pvDel:hover{border-color:#bc0404;color:#bc0404}
#pv.full .pvscroll{right:1px}
#pv.full .pvscroll i{width:3px;background:rgba(0,0,0,.3)}
/* 电脑端全屏：复用手机旋转预览的胶囊顶栏/底栏（居中悬浮、两栏同宽，JS 同步宽度） */
@media(min-width:901px){
 #pv.full .bar,#pv.full .foot{left:50%;right:auto;transform:translateX(-50%);
  width:max-content;max-width:none;height:48px;flex-wrap:nowrap;
  padding:0 12px;border:0;border-radius:999px}
 #pv.full .bar{top:12px}
 #pv.full .foot{bottom:12px}
 #pv.full .foot button{border-radius:999px}
 #pv.full .bar button{width:34px;height:34px;border-radius:50%}
 /* 窗口预览：顶栏/底栏回到 flex 流，与图片顶边/底边对齐，不再覆盖图片 */
 #pv:not(.full) .bar,#pv:not(.full) .foot{position:relative;inset:auto}
}
@media(max-width:900px){
 /* 手机端底栏图标间距比电脑端小 10px；竖屏图标圆形边框 */
 #pv .foot{gap:18px}
 #pv.full .foot button{border-radius:999px}
 /* 手机端直接全屏，无需全屏/退出全屏按钮 */
 #pv .foot #pvFull{display:none}
 /* 手机端显示旋转按钮：逆时针在左、顺时针在右（覆盖底栏隐藏规则） */
 #pv .foot #pvRotCcw,#pv .foot #pvRot{display:inline-flex}
 /* 手机端显示左右切图按钮，贴合图片两侧（JS 计算坐标） */
 #pv.full .pvn{display:inline-flex;width:30px;height:30px}
 #pv.full .pvn svg{width:16px;height:16px}
}
/* 深色模式：预览栏元素改亮色，避免与深色背景融为一体 */
html.theme-dark #pv .bar button,html.theme-dark #pv .foot button,
html.theme-dark #pv .bar button:hover,html.theme-dark #pv .foot button:hover,
html.theme-dark #pv.full .bar button,html.theme-dark #pv.full .foot button,
html.theme-dark #pv.full .bar button:hover,html.theme-dark #pv.full .foot button:hover{
 background:transparent;border-color:#fff;color:#fff}
html.theme-dark #pv .bar #pvTitle,html.theme-dark #pv.full .bar #pvTitle{color:#fff}
html.theme-dark #pv .foot #pvDel,html.theme-dark #pv .foot #pvDel:hover,
html.theme-dark #pv.full .foot #pvDel,html.theme-dark #pv.full .foot #pvDel:hover{border-color:#ff6b6b;color:#ff6b6b}
/* 旋转横屏：卡片按横屏尺寸布局后整张转 90°，顶栏/图片/底栏一起转且铺满视口 */
@media(max-width:900px){
 #pv.rot90 .card,#pv.rot270 .card{position:absolute;left:50%;top:50%;flex:none;
  width:100vh;height:100vw;max-width:none;max-height:none}
 #pv.rot90 .card{transform:translate(-50%,-50%) rotate(90deg)}
 #pv.rot270 .card{transform:translate(-50%,-50%) rotate(-90deg)}
 #pv.rot180 .card{transform:rotate(180deg)}
 /* 旋转后顶栏/底栏：宽度以底栏四按钮为准、两栏同宽（JS 同步），胶囊悬浮在图片上层 */
 #pv.rot90 .bar,#pv.rot270 .bar,
 #pv.rot90 .foot,#pv.rot270 .foot{left:50%;right:auto;transform:translateX(-50%);
  width:max-content;height:48px;max-width:none;flex-wrap:nowrap;
  padding:0 12px;border:0;border-radius:999px}
 #pv.rot90 .bar,#pv.rot270 .bar{top:12px}
 #pv.rot90 .foot,#pv.rot270 .foot{bottom:12px}
 /* 旋转后底栏四按钮胶囊边框、顶栏两图标圆形边框 */
 #pv.rot90 .foot button,#pv.rot270 .foot button{border-radius:999px}
 #pv.rot90 .bar button,#pv.rot270 .bar button{width:34px;height:34px;border-radius:50%}
 /* 两栏悬浮覆盖在图片上层：旋转后内容区铺满整张卡片 */
 #pv.rot90 .body,#pv.rot270 .body{top:0;bottom:0}
 /* 图片铺满窗口，按横屏视口等比缩放不裁切 */
 #pv.rot90 .frame,#pv.rot270 .frame{width:100%;height:100%}
 #pv.rot90 #pvImg,#pv.rot270 #pvImg{width:100%;height:100%;max-width:none;max-height:none;
  margin-left:0;object-fit:contain}
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
<div class="stat"><div class="k">接口 / 图片</div><div class="v">$apicount 个接口 · $imgcount 张图片</div></div>
<div class="stat"><div class="k">网关入口</div><div class="v $gwclass">$gwstate</div></div>
<div class="stat"><div class="k">Wallhaven API Key</div><div class="v" id="ovKey">—</div></div>
<div class="stat"><div class="k">目录状态</div><div class="v $stateclass">$state</div></div>
<div class="stat"><div class="k">一致性体检</div><div class="v" id="ovCheck">—</div></div>
<div class="stat"><div class="k">壁纸采集任务</div><div class="v" id="ovFetch">—</div></div>
<div class="stat"><div class="k">图片压缩任务</div><div class="v" id="ovZip">—</div></div>
<div class="stat"><div class="k">服务端口</div><div class="v">$port</div></div>
<div class="stat"><div class="k">版本号</div><div class="v">v$version</div></div>
</div></div></div>
</section>

<section class="panel" id="panel-api">
<div class="card c-api"><h2>接口列表</h2><div class="card-body"><div class="apis">$rows</div></div></div>
</section>

<section class="panel" id="panel-set">
<div class="card c-set"><h2>设置</h2><div class="card-body">
<div class="grid theme-grid">
<div class="sm"><label for="f_port">服务端口</label><input id="f_port" type="number" min="1024" max="65535" value="$port"></div>
<div class="grow"><label for="f_root">图片根目录（留空=自动使用已授权目录）</label>
<input id="f_root" type="text" value="$root_value" placeholder="留空即自动跟随应用权限中授权的文件夹"></div>
<div class="sm"><label for="f_ttl">缓存秒数</label><input id="f_ttl" type="number" min="1" max="3600" value="$ttl"></div>
<div class="btnrow" style="display:flex;align-items:center;gap:8px;flex:1 1 330px;min-width:0"><button class="primary" id="save">保存并应用</button>
<button id="reload">立即刷新</button>
<button id="consistency" title="只读检查索引、删除、拉黑三者是否有偏差，不修改任何文件">一致性体检<span id="chkicon" class="chkicon" title="点击查看体检详情" role="button" tabindex="0"></span></button></div>
</div>
<div id="checkmsg" class="cfgmsg"></div>
<div id="cfgmsg" class="cfgmsg"></div>
<div id="msg"></div>
<div class="cleanup-row" style="margin-top:14px"><label>清理自传图副本<input type="checkbox" id="f_cleanup_uploads"$cupchecked></label>
<span class="kv">开启后，删除自传图或点魔术师时会按内容指纹同步清理其他目录里的相同图片（关闭时只清理采集图）</span></div>
<div class="theme-row"><label>主题模式</label>
<div class="tset" id="f_theme" data-v="auto"><div class="tcur" id="f_theme_cur">跟随系统</div>
<div class="topts"><div class="topt" data-v="auto">跟随系统</div>
<div class="topt" data-v="light">浅色</div><div class="topt" data-v="dark">深色</div></div></div></div>
</div></div>
</section>

<section class="panel" id="panel-wall">
<div class="card c-wall"><h2>Wallhaven壁纸采集</h2><div class="card-body">
<div class="apikeybox">
<label for="api_key">Wallhaven API Key<span class="keydot" id="keystate" title="检测中…"></span></label>
<div class="frow"><input id="api_key" type="password" placeholder="留空并保存=清除 Key，仅可下载SFW">
<button class="primary" id="keysave"><svg viewBox="0 0 24 24"><path d="M19 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h11l5 5v11a2 2 0 0 1-2 2z"/><polyline points="17 21 17 13 7 13 7 21"/><polyline points="7 3 7 8 15 8"/></svg>保存</button></div>
</div>
<div id="tasklist"></div>
<div class="frow"><button class="primary" id="tnew">+ 新建任务</button></div>
<details id="tformbox" style="margin-top:14px"><summary style="cursor:pointer;font-size:13px;color:#656d76">任务参数与筛选条件</summary>
<div class="grid eqrow">
<div><label for="t_name">任务名称</label><input id="t_name" type="text" placeholder="例如 每日动漫壁纸"></div>
<div><label for="t_target">目标分类（子文件夹名）</label><input id="t_target" type="text" value="Wallhaven"></div>
<div><label for="t_count">每次下载张数（最多 480）</label><input id="t_count" type="number" min="1" max="480" value="24" oninput="if(this.value!==''&&+this.value>480)this.value=480"></div>
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
<div class="eq"><label for="t_start">起始页码<span class="hint">0=随机起点</span></label><input id="t_start" type="number" min="0" max="500" value="0"></div>
<div class="eq"><label for="t_end">结束页码<span class="hint">0=不限 · 单次最多翻100页</span></label><input id="t_end" type="number" min="0" max="500" value="0"></div>
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
<label><input type="checkbox" id="z_fullbackup">全量备份</label>
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
<div class="card c-help"><div id="helpbox"><div class="help-summary">使用说明</div><div class="help-body">
<p class="meta"><b>新增接口</b>：图库里新建子文件夹并放入图片，最多等 $ttl 秒自动生效；结构为 <code>分类名/*.jpg</code>，接口名不区分大小写。</p>
<p class="meta"><b>缓存</b>：只缓存目录扫描结果 $ttl 秒，不缓存图片；采集、压缩、删图会自动更新，外部改动后点「立即刷新」即时生效。</p>
<p class="meta"><b>复制地址</b>：给出随机接口，跟随当前域名/IP，端口固定为 $port，可直接外链；网关地址 <code>$gwurl</code> 仅登录态可用。</p>
<p class="meta"><b>打开看看</b>：按下载时间由近到远看图、可滑动切换，左下角显示图片 ID（自传图为文件名前 6 位）；「删除」会拉黑并同步清掉其他目录的同 ID 副本；「魔术师」全局清理所有目录和备份目录中已拉黑的采集图，任务运行中会暂缓。</p>
<p class="meta"><b>清理自传图</b>：设置里开启后，删除自传图或点魔术师时会按内容指纹同步清理其他目录里的相同自传图（采集图不受影响）；关闭时只清理采集图。</p>
<p class="meta"><b>采集任务</b>：周几全不选=单次、勾选=每周定时；按接口顺序下载、只取原图，已下载 ID 记入 <code>downloaded.txt</code>（该文件只记录当前存在的图片，删图时自动移除对应 ID）；任务开始前自动补拉黑外部删除的图并清理其失效记录；无 API Key 时强制仅 SFW。</p>
<p class="meta"><b>压缩任务</b>：源目录图片转 JPG，短边超限则缩小、体积超限则降质，原图备份一次；采集图备份时同步登记进备份目录的 <code>downloaded.txt</code>（索引=该目录现存图片，删图时自动移除）。用系统 ffmpeg。源目录与备份目录需在应用权限中授权。</p>
<p class="meta"><b>一致性体检</b>：设置页可只读检查黑名单、下载记录与图片文件的偏差，不改动任何文件。</p>
<p class="meta">接口 <a href="$base/_apis">/_apis</a> · 健康检查 <a href="$base/_health">/_health</a></p>
</div></div></div>
</section>
</main></div>
<script>
var BASE='$base', GATEWAY=$gateway, DIRECT='$direct', PORT=$port, CLEANUP_UPLOADS=$cleanupuploads;
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
var pvEl=null,pvP='',pvStage=0,pvSeq=0,pvIdx=0,pvTotal=0,pvRot=0;
var PV_NOREMIND='ranpix_del_noremind';
var PV_ICO_FS='<svg viewBox="0 0 24 24"><path d="M8 3H3v5M16 3h5v5M8 21H3v-5M16 21h5v-5"/></svg>',
 PV_ICO_FSEXIT='<svg viewBox="0 0 24 24"><path d="M3 8h5V3M21 8h-5V3M3 16h5v5M21 16h-5v5"/></svg>',
 PV_ICO_X='<svg viewBox="0 0 24 24"><path d="M6 6l12 12M18 6L6 18"/></svg>',
 PV_ICO_MAGIC='<svg viewBox="0 0 24 24"><g transform="translate(-1 1)"><path d="m12 2 1.9 6.1L20 10l-6.1 1.9L12 18l-1.9-6.1L4 10l6.1-1.9z"/><path d="M19 16v4M21 18h-4"/></g></svg>',
 PV_ICO_DEL='<svg viewBox="0 0 24 24"><path d="M4 7h16M10 11v6M14 11v6M5 7l1 13h12l1-13M9 7V4h6v3"/></svg>',
 PV_ICO_PREV='<svg viewBox="0 0 24 24"><path d="M15 5l-7 7 7 7"/></svg>',
 PV_ICO_NEXT='<svg viewBox="0 0 24 24"><path d="M9 5l7 7-7 7"/></svg>',
 PV_ICO_ROT='<svg viewBox="0 0 24 24" style="fill:currentColor;stroke:none"><path d="M17.65 6.35A7.958 7.958 0 0 0 12 4c-4.42 0-7.99 3.58-7.99 8s3.57 8 7.99 8c3.73 0 6.84-2.55 7.73-6h-2.08A5.99 5.99 0 0 1 12 18c-3.31 0-6-2.69-6-6s2.69-6 6-6c1.66 0 3.14.69 4.22 1.78L13 11h7V4l-2.35 2.35z"/></svg>',
 PV_ICO_ROT_CCW='<svg viewBox="0 0 24 24" style="fill:currentColor;stroke:none"><path d="M12 5V1L7 6l5 5V7c3.31 0 6 2.69 6 6s-2.69 6-6 6-6-2.69-6-6H4c0 4.42 3.58 8 8 8s8-3.58 8-8-3.58-8-8-8z"/></svg>';
function pvClose(){if(pvEl&&pvEl.parentNode){pvEl.parentNode.removeChild(pvEl)}pvEl=null;pvRot=0;}
/* 旋转后顶栏/底栏同宽：以底栏四按钮的实际宽度为准，避免两栏过宽 */
function pvSyncRotBar(){
  if(!pvEl)return;
  var bar=pvEl.querySelector('.bar'),foot=pvEl.querySelector('.foot');
  if(!bar||!foot)return;
  /* 手机旋转态、电脑端全屏：胶囊顶栏/底栏同宽，均以底栏按钮为准 */
  var desktop=window.matchMedia&&window.matchMedia('(min-width:901px)').matches;
  var desktopFull=pvEl.classList.contains('full')&&desktop;
  /* 电脑窗口预览旋转时底栏保持原宽，不走胶囊同宽分支；手机旋转与电脑全屏仍同宽 */
  if((!desktop&&(pvRot===90||pvRot===270))||desktopFull){
    /* 底栏保持 max-content 自然宽度（按钮必在一行），顶栏取同宽 */
    foot.style.width='';bar.style.width='';
    var w=foot.offsetWidth;
    bar.style.width=w+'px';
  }else{bar.style.width='';foot.style.width='';}
}
/* 电脑全屏：左右切图按钮贴图片实际绘制区两侧，居中对齐；其余模式回退 CSS 静态定位 */
function pvSyncNav(){
  if(!pvEl)return;
  var a=pvEl.querySelector('#pvNavPrev'),b=pvEl.querySelector('#pvNavNext'),
      img=document.getElementById('pvImg'),card=pvEl.querySelector('.card');
  if(!a||!b||!img||!card)return;
  var clear=function(){[a,b].forEach(function(e){e.style.left='';e.style.top='';e.style.right='';});};
  if(!pvEl.classList.contains('full')){clear();return;}
  var mobile=window.matchMedia&&window.matchMedia('(max-width:900px)').matches;
  if(!mobile){
    /* 电脑全屏：按视口 rect 贴图片两侧 */
    var ir=img.getBoundingClientRect(),cr=card.getBoundingClientRect();
    if(!ir.width||!ir.height){clear();return;}
    var cy=Math.round(ir.top-cr.top+ir.height/2);
    a.style.left=Math.round(ir.left-cr.left+14)+'px';a.style.top=cy+'px';a.style.right='auto';
    b.style.left=Math.round(ir.right-cr.left-14-b.offsetWidth)+'px';b.style.top=cy+'px';b.style.right='auto';
    return;
  }
  /* 手机端：按 offset 链（不受旋转 transform 影响）+ contain 绘制区贴两侧 */
  var bw=img.offsetWidth,bh=img.offsetHeight;
  if(!bw||!bh){clear();return;}
  var nw=img.naturalWidth||bw,nh=img.naturalHeight||bh;
  var s=Math.min(bw/nw,bh/nh),dw=nw*s,dh=nh*s;
  var ox=0,oy=0,n=img;
  while(n&&n!==card){ox+=n.offsetLeft;oy+=n.offsetTop;n=n.offsetParent;}
  if(n!==card){clear();return;}
  var ix=ox+(bw-dw)/2,iy=oy+(bh-dh)/2,cy2=Math.round(iy+dh/2);
  a.style.left=Math.round(ix+10)+'px';a.style.top=cy2+'px';a.style.right='auto';
  b.style.left=Math.round(ix+dw-10-b.offsetWidth)+'px';b.style.top=cy2+'px';b.style.right='auto';
}
/* 手机端：角标贴合图片实际绘制区域四角（用 offset 定位，不受旋转 transform 影响） */
function pvSyncBadges(){
  if(!pvEl)return;
  pvSyncNav();
  var t=document.getElementById('pvTitle'),x=document.getElementById('pvX'),i=document.getElementById('pvIdx'),d=document.getElementById('pvId'),img=document.getElementById('pvImg');
  if(!t||!x||!i||!d||!img)return;
  var clear=function(){[t,x,i,d].forEach(function(e){e.style.left='';e.style.top='';e.style.right='';e.style.bottom='';});};
  var mobile=window.matchMedia&&window.matchMedia('(max-width:900px)').matches;
  var full=pvEl.classList.contains('full');
  /* 电脑窗口预览：角标挂在滚动容器外的 bwrap 上，CSS 静态贴图片区四角，滚动时天然静止 */
  if(!mobile&&!full){clear();return;}
  var wrap=pvEl.querySelector('.bwrap'),bw=img.offsetWidth,bh=img.offsetHeight;
  if(!wrap||!bw||!bh){clear();return;}
  var px,py,dw,dh;
  if(full&&!mobile){
    /* 电脑全屏：图片在视口内居中留白，按实际绘制矩形贴角（此模式不旋转，rect 即局部坐标） */
    var ir=img.getBoundingClientRect(),wr=wrap.getBoundingClientRect();
    px=ir.left-wr.left;py=ir.top-wr.top;dw=ir.width;dh=ir.height;
  }else{
    /* 手机端：bwrap 与图片区同框，但图片等比缩放后四周可能有留白，按实际绘制区贴角 */
    var nw=img.naturalWidth||bw,nh=img.naturalHeight||bh;
    var s=Math.min(bw/nw,bh/nh);dw=nw*s;dh=nh*s;
    px=img.offsetLeft+(bw-dw)/2;py=img.offsetTop+(bh-dh)/2;
  }
  var place=function(e,l,p){e.style.left=Math.round(l)+'px';e.style.top=Math.round(p)+'px';e.style.right='auto';e.style.bottom='auto';};
  place(t,px+8,py+8);
  place(x,px+dw-8-x.offsetWidth,py+8);
  place(d,px+8,py+dh-8-d.offsetHeight);
  place(i,px+dw-8-i.offsetWidth,py+dh-8-i.offsetHeight);
}
/* 旋转图标：电脑端两按钮常驻、图标固定（累加±90）；手机端沿用三态（转后只留一个还原按钮） */
function pvSyncRotIcons(){
  var cw=document.getElementById('pvRot'),ccw=document.getElementById('pvRotCcw');
  if(!cw||!ccw)return;
  var desktop=window.matchMedia&&window.matchMedia('(min-width:901px)').matches;
  if(desktop){
    cw.innerHTML=PV_ICO_ROT;cw.title='向右旋转90°';cw.style.display='';
    ccw.innerHTML=PV_ICO_ROT_CCW;ccw.title='向左旋转90°';ccw.style.display='';
    return;
  }
  if(pvRot===0){
    cw.innerHTML=PV_ICO_ROT;cw.title='顺时针旋转';cw.style.display='';
    ccw.innerHTML=PV_ICO_ROT_CCW;ccw.title='逆时针旋转';ccw.style.display='';
  }else if(pvRot===90){
    /* 顺时针后：顺时针按钮变逆时针图标用于还原，逆时针按钮隐藏 */
    cw.innerHTML=PV_ICO_ROT_CCW;cw.title='还原旋转';cw.style.display='';
    ccw.style.display='none';
  }else{
    /* 逆时针后：逆时针按钮变顺时针图标用于还原，顺时针按钮隐藏 */
    ccw.innerHTML=PV_ICO_ROT;ccw.title='还原旋转';ccw.style.display='';
    cw.style.display='none';
  }
}
/* 清除电脑端「只转图片」写入的内联样式，恢复常规布局 */
function pvClearDeskRot(){
  if(!pvEl)return;
  var body=pvEl.querySelector('.body'),frame=pvEl.querySelector('.frame'),img=document.getElementById('pvImg');
  if(body)body.style.height='';
  if(frame){
    frame.style.position='';frame.style.left='';frame.style.top='';frame.style.width='';
    frame.style.height='';frame.style.overflow='';frame.style.display='';
    frame.style.alignItems='';frame.style.justifyContent='';frame.style.padding='';
  }
  if(img){
    img.style.width='';img.style.height='';img.style.maxWidth='';img.style.maxHeight='';
    img.style.margin='';img.style.marginLeft='';img.style.marginRight='';
    img.style.transform='';img.style.transformOrigin='';
  }
}
function pvApplyRot(){
  if(!pvEl)return;
  pvEl.classList.remove('rot90','rot180','rot270');
  pvClearDeskRot();
  var img=document.getElementById('pvImg');
  var body=pvEl.querySelector('.body'),frame=pvEl.querySelector('.frame');
  var desktop=window.matchMedia&&window.matchMedia('(min-width:901px)').matches;
  if(desktop&&pvRot&&img&&body&&frame){
    /* 电脑端：只旋转图片本体，顶栏/底栏/角标/切图按钮保持正立。
       关键：去掉旧版 frame padding / 宽度减 28 / 高度减 100 的人为内缩（宽白边的来源），
       旋转后按与旋转前一致的铺满规则重算尺寸，做到贴边。 */
    var full=pvEl.classList.contains('full');
    var nw=img.naturalWidth||1,nh=img.naturalHeight||1;
    var vert=(pvRot===90||pvRot===270);
    var vw=vert?nh:nw, vh=vert?nw:nh;   /* 旋转后视觉宽高 */
    var aw=Math.max(1,body.clientWidth),ah=Math.max(1,body.clientHeight);
    /* 窗口预览：旋转前图片是宽度撑满，旋转后同样按宽度撑满（左右贴边），高度按比例。
       注意不能用旋转前已被图片撑起的 body.clientHeight 做 contain——那一转就会越缩越小。
       全屏预览：内容区高度固定，按 contain 铺满（至少一边贴边），和旋转前表现一致。 */
    var s=full?Math.min(aw/vw, ah/vh):aw/vw;
    var showH=Math.round(vh*s);
    if(!full){
      /* 窗口预览：旋转后内容区贴合图片视觉高度（不再固定 innerHeight-40 留下大片空白）。
         超高时截到视口高度，靠 body 滚动看全，避免顶部溢出滚不到。 */
      var cap=Math.max(120,window.innerHeight-40);
      body.style.height=Math.min(showH,cap)+'px';
    }
    frame.style.position='absolute';frame.style.left='0';frame.style.top='0';
    frame.style.width='100%';frame.style.height='100%';frame.style.overflow='visible';
    frame.style.display='flex';
    frame.style.alignItems=(!full&&showH>body.clientHeight)?'flex-start':'center';
    frame.style.justifyContent='center';
    frame.style.padding='0';
    img.style.width=Math.round(nw*s)+'px';img.style.height=Math.round(nh*s)+'px';
    img.style.maxWidth='none';img.style.maxHeight='none';
    img.style.margin='0';img.style.marginLeft='0';img.style.marginRight='0';
    img.style.transformOrigin='center center';
    img.style.transform='rotate('+pvRot+'deg)';
  }else if(pvRot){
    /* 手机端：沿用整卡旋转 */
    pvEl.classList.add('rot'+pvRot);
  }
  pvSyncRotIcons();
  setTimeout(function(){pvSyncScroll();pvSyncRotBar();pvSyncBadges();},0);
}
function pvRotate(dir){
  var desktop=window.matchMedia&&window.matchMedia('(min-width:901px)').matches;
  if(desktop){
    /* 电脑端：每次累加±90°（dir 为 90/270，270 即 -90°），可连续转到 180/270 再回 0 */
    pvRot=(pvRot+dir)%360;
  }else{
    /* 手机端：转一次后再点任一方向还原 */
    pvRot=pvRot===0?dir:0;
  }
  pvApplyRot();
}
/* 全屏看图：切换弹层铺满视口；按钮图标在「展开/收起」间切换 */
function pvFullToggle(){
  if(!pvEl)return;
  var on=pvEl.classList.toggle('full');
  var b=document.getElementById('pvFull');if(b){b.innerHTML=on?PV_ICO_FSEXIT:PV_ICO_FS;b.title=on?'退出全屏':'全屏';}
  if(pvRot)pvApplyRot();  /* 旋转态下内容区尺寸变了，重算图片 contain */
  setTimeout(function(){pvSyncScroll();pvSyncRotBar();pvSyncBadges();},0);
}
function pvSyncScroll(){
  if(!pvEl)return;
  var b=pvEl.querySelector('.body'),t=pvEl.querySelector('.pvscroll i');
  if(!b||!t)return;
  var max=b.scrollHeight-b.clientHeight;
  if(max<=2){t.style.display='none';return;}
  t.style.display='block';
  var h=Math.max(24,Math.round(b.clientHeight*b.clientHeight/b.scrollHeight));
  var y=Math.round((b.scrollTop/max)*(b.clientHeight-h));
  t.style.height=h+'px';t.style.transform='translateY('+y+'px)';
}
function pvResetDel(){var b=document.getElementById('pvDel');if(b){b.disabled=false;b.innerHTML=PV_ICO_DEL;b.title='删除';}}
function pvLoad(){
  pvResetDel();
  var img=document.getElementById('pvImg'),err=document.getElementById('pvErr');
  pvStage=0;err.style.display='none';img.style.display='';
  pvSeq++;
  var seq=pvSeq;
  /* 预览按下载时间由近到远顺序浏览；复制链接始终是不带参数的随机接口 */
  var q='order=recent&i='+pvIdx+'&_='+Date.now()+'-'+seq;
  img.src=gwUrl(pvP)+'?'+q;
  var n=document.getElementById('pvIdx');
  if(n){var shown=pvTotal?(pvIdx%pvTotal)+1:pvIdx+1;n.textContent=shown+'/'+(pvTotal||'?');}
  /* 左下角图片标识：采集图显示 wallhaven ID，自传图显示文件名前 6 位 */
  var d=document.getElementById('pvId');if(d)d.textContent='';
  fetch(BASE+'/_preview_label?cat='+encodeURIComponent(pvP)+'&i='+pvIdx+'&_='+Date.now()+'-'+seq)
   .then(function(r){return r.json()}).then(function(j){
     if(seq!==pvSeq)return;                       /* 快速切图时只接受最后一次 */
     var el=document.getElementById('pvId');
     if(el&&j&&j.ok)el.textContent=j.label||'';
     pvSyncBadges();
   }).catch(function(){});
  setTimeout(pvSyncScroll,0);
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
function pvAsk(title,desc,showCheck,okText,onYes,danger){
  var box=document.getElementById('pvCfm');if(!box)return;
  var ct=document.getElementById('pvCfmt');
  ct.textContent=title;ct.style.color=danger?'#d92d20':'';
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
    pvEl.innerHTML='<div class="card">'+
      '<div class="bwrap"><div class="body"><div class="frame"><img id="pvImg" alt="">'+
      '</div>'+
      '<div id="pvErr" class="err" style="display:none"></div></div>'+
      '<div class="pvscroll"><i></i></div>'+
      '<button id="pvX" type="button" title="关闭">'+PV_ICO_X+'</button>'+
      '<span id="pvTitle"></span><span id="pvId" class="pvcount"></span><span id="pvIdx" class="pvcount"></span></div>'+
      '<button id="pvNavPrev" class="pvn prev" type="button" title="上一张">'+PV_ICO_PREV+'</button>'+
      '<button id="pvNavNext" class="pvn next" type="button" title="下一张">'+PV_ICO_NEXT+'</button>'+
      '<div class="foot"><button id="pvMagic" type="button" title="魔术师">'+PV_ICO_MAGIC+'</button>'+
      '<button id="pvDel" class="danger" type="button" title="删除">'+PV_ICO_DEL+'</button>'+
      '<button id="pvRotCcw" type="button" title="逆时针旋转">'+PV_ICO_ROT_CCW+'</button>'+
      '<button id="pvRot" type="button" title="顺时针旋转">'+PV_ICO_ROT+'</button>'+
      '<button id="pvFull" type="button" title="全屏">'+PV_ICO_FS+'</button></div>'+
      '<div id="pvCfm" class="cfm" style="display:none"><div class="cfmcard">'+
      '<div class="cfmt" id="pvCfmt"></div><div class="cfmd" id="pvCfmd"></div>'+
      '<label class="cfmk" id="pvCfmk"><input type="checkbox" id="pvNoRemind">不再提醒</label>'+
      '<div class="cfmact"><button id="pvCfmNo" type="button">取消</button>'+
      '<button id="pvCfmYes" class="danger" type="button">删除</button></div></div></div></div>';
    document.body.appendChild(pvEl);
    pvEl.addEventListener('click',function(e){if(e.target===pvEl)pvClose()});
    document.getElementById('pvX').onclick=function(e){e.stopPropagation();pvClose();};
    document.getElementById('pvFull').onclick=pvFullToggle;
    document.getElementById('pvNavPrev').onclick=function(e){e.stopPropagation();pvPrev();};
    document.getElementById('pvNavNext').onclick=function(e){e.stopPropagation();pvNext();};
    document.getElementById('pvDel').onclick=function(){pvDelete()};
    document.getElementById('pvMagic').onclick=function(){pvMagic()};
    document.getElementById('pvRotCcw').onclick=function(){pvRotate(270)};
    document.getElementById('pvRot').onclick=function(){pvRotate(90)};
    document.getElementById('pvImg').onerror=function(){pvFail()};
    /* 手机端手势：左滑下一张、右滑上一张；旋转后方向随卡片一起转 */
    var bEl=pvEl.querySelector('.body'),tsX=0,tsY=0;
    bEl.addEventListener('scroll',function(){pvSyncScroll();pvSyncBadges();});
    document.getElementById('pvImg').onload=function(){pvApplyRot();pvSyncScroll()};
    window.addEventListener('resize',function(){pvApplyRot();pvSyncScroll()});
    bEl.addEventListener('touchstart',function(e){
      if(e.touches.length===1){tsX=e.touches[0].clientX;tsY=e.touches[0].clientY;}
    },{passive:true});
    bEl.addEventListener('touchend',function(e){
      if(!e.changedTouches||e.changedTouches.length!==1)return;
      var dx=e.changedTouches[0].clientX-tsX,dy=e.changedTouches[0].clientY-tsY;
      var along,across;
      if(pvRot===90){along=dy;across=dx;}
      else if(pvRot===270){along=-dy;across=-dx;}
      else{along=dx;across=dy;}
      if(Math.abs(along)<45||Math.abs(along)<Math.abs(across)*1.4)return;
      if(along<0)pvNext();else pvPrev();
    },{passive:true});
    /* 电脑端看图：点击图片区左半边上一张、右半边下一张（全屏与非全屏均可） */
    bEl.addEventListener('click',function(e){
      if(!pvEl)return;
      if(!window.matchMedia||!window.matchMedia('(hover:hover) and (pointer:fine)').matches)return;
      var cfm=document.getElementById('pvCfm');if(cfm&&cfm.style.display==='flex')return;
      if(e.clientX<window.innerWidth/2)pvPrev();else pvNext();
    });
    /* 电脑端看图：键盘左右方向键切图（左=上一张，右=下一张），全屏与非全屏均可。
       挂在 document 上一次即可；预览关闭时 pvEl 为 null 直接返回；确认框弹出或输入框聚焦时不抢键。 */
    document.addEventListener('keydown',function(e){
      if(!pvEl||!pvEl.parentNode)return;
      if(e.key!=='ArrowLeft'&&e.key!=='ArrowRight')return;
      if(!window.matchMedia||!window.matchMedia('(hover:hover) and (pointer:fine)').matches)return;
      var cfm=document.getElementById('pvCfm');if(cfm&&cfm.style.display==='flex')return;
      var tag=(e.target&&e.target.tagName||'').toLowerCase();
      if(tag==='input'||tag==='textarea'||tag==='select')return;
      e.preventDefault();
      if(e.key==='ArrowLeft')pvPrev();else pvNext();
    });
  }
  /* 手机端直接进全屏预览；电脑端仍用窗口预览 */
  var wantFull=window.matchMedia&&window.matchMedia('(max-width:900px)').matches;
  if(wantFull!==pvEl.classList.contains('full'))pvFullToggle();
  document.getElementById('pvTitle').textContent='最近下载';
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
       if(!j.ok){btn.disabled=false;btn.title='删除失败，可重试';msg('删除失败：'+(j.error||'未知错误'),'warn');return;}
       /* 只删当前这张时不展示任何多余状态，直接切下一张；
          发生跨目录联动时给一次性提示，并修正当前接口可能被连带删掉的数量。 */
       if(pvTotal>0)pvTotal=Math.max(0,pvTotal-1-(j.synced_cat||0));
       if(j.synced)msg('已同步清理 '+j.synced+' 张相同图片'+(j.synced_failed?('，'+j.synced_failed+' 张失败'):''));
       pvLoad();
     }).catch(function(e){btn.disabled=false;btn.title='删除失败，可重试';msg('请求失败：'+e,'warn')});
  };
  var silent=false;try{silent=localStorage.getItem(PV_NOREMIND)==='1'}catch(e){}
  if(silent){go();return;}
  var tip=CLEANUP_UPLOADS
    ? '采集图会加入黑名单；自传图按内容指纹记录墓碑。其他目录里的同一张图会一起删除。'
    : '加入全局黑名单，其他目录里的同一张采集图也会一起删除，以后采集任务扫到自动跳过。自传图只删当前这一张。';
  pvAsk('删除这张图片？',tip,true,'删除',go);
}
/* 魔术师：① 把「downloaded.txt 有记录但文件已被外部删除」的 ID 补入黑名单；
   ② 全局删除所有分类和备份目录里 ID 已进黑名单的采集图（自传图无 ID，不会被删） */
function pvMagic(){
  var btn=document.getElementById('pvMagic');if(!btn||btn.disabled)return;
  var tip=CLEANUP_UPLOADS
    ? '采集图会加入黑名单；自传图按内容指纹记录墓碑。其他目录里的同一张图会一起删除。'
    : '加入全局黑名单，其他目录里的同一张采集图也会一起删除，以后采集任务扫到自动跳过。自传图只删当前这一张。';
  var normalDesc='① 扫描所有分类，把已下载但文件已不在的条目补入全局黑名单并清理失效下载记录；② 全局删除所有分类和备份目录里已进黑名单的图片。'
    +(CLEANUP_UPLOADS?'③ 同时按内容指纹清理之前删过的自传图副本。':'你自己上传的图片不会被删除。');
  var run=function(){
    var old=btn.title||'魔术师';btn.disabled=true;btn.title='处理中…';
    fetch(BASE+'/_image/magician',{method:'POST',
      headers:{'Content-Type':'application/x-www-form-urlencoded'},
      body:'cat='+encodeURIComponent(pvP)})
     .then(function(r){return r.json()}).then(function(j){
       btn.disabled=false;btn.title=old;
       if(!j.ok){pvAsk('魔术师失败',j.error||'未知错误',false,'知道了',null);return;}
       /* 当前接口图片被删后重新取总数、回到第一张，避免数字错位 */
       pvTotal=j.remaining;pvIdx=0;
       pvAsk('魔术师完成',
         '补拉黑：新拉黑 '+j.added+' 个 ID（黑名单共 '+j.total+' 个）；全局清理：共删除 '+j.removed+' 张（采集图 '+j.collected_removed+' / 自传图 '+j.upload_removed+'；当前接口 '+j.in_category+' 张，备份目录 '+j.in_backup+' 张）；同步清理失效下载记录 '+j.records_removed+' 条'+(j.failed?('，失败 '+j.failed+' 张'):'')+'。',
         false,'知道了',function(){pvLoad()});
     }).catch(function(e){btn.disabled=false;btn.title=old;pvAsk('魔术师失败',String(e),false,'知道了',null)});
  };
  var ask=function(est){
    if(est>=50){
      pvAsk('大批量清理 · 请确认',
        '本次预计清理约 '+est+' 张已拉黑的图片（各分类目录与备份目录中的副本），删除后不可恢复。'+tip,
        false,'确认清理 '+est+' 张',run,true);
    }else{
      pvAsk('魔术师 · 批量拉黑并清理',normalDesc,false,'开始',run);
    }
  };
  /* 先只读预估清理量，量大时升级为红色警告；统计失败仍按普通确认执行，不阻断功能 */
  fetch(BASE+'/_consistency',{cache:'no-store'})
    .then(function(r){return r.json()})
    .then(function(j){ask((j.in_blacklist_with_file||0)+(j.backup_blacklist_hits||0))})
    .catch(function(){ask(0)});
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
/* 主题模式：切换即时生效并写入配置，无需重启 */
(function(){
  var box=document.getElementById('f_theme');
  if(!box)return;
  var cur=document.getElementById('f_theme_cur');
  var opts=box.querySelectorAll('.topt');
  var labels={auto:'跟随系统',light:'浅色',dark:'深色'};
  var v=document.documentElement.getAttribute('data-theme')||'auto';
  if(!labels[v])v='auto';
  function setVal(nv){
    box.setAttribute('data-v',nv);
    cur.textContent=labels[nv];
    for(var k=0;k<opts.length;k++)opts[k].classList.toggle('on',opts[k].getAttribute('data-v')===nv);
  }
  function choose(nv){
    setVal(nv);box.classList.remove('open');
    if(window.rpTheme)window.rpTheme(nv);
    cfgMsg('主题已切换（仅本机）','ok');
  }
  setVal(v);
  cur.onclick=function(e){e.stopPropagation();box.classList.toggle('open');};
  for(var i=0;i<opts.length;i++)(function(o){
    o.onclick=function(e){e.stopPropagation();choose(o.getAttribute('data-v'));};
  })(opts[i]);
  document.addEventListener('click',function(){box.classList.remove('open');});
})();
document.getElementById('save').onclick=function(){
  var btn=this;btn.disabled=true;cfgMsg('正在保存…','');
  var enc=encodeURIComponent;
  var body='port='+enc(document.getElementById('f_port').value)
    +'&image_root='+enc(document.getElementById('f_root').value)
    +'&cache_ttl='+enc(document.getElementById('f_ttl').value)
    +'&cleanup_uploads='+(document.getElementById('f_cleanup_uploads').checked?'1':'0');
  fetch(BASE+'/_config',{method:'POST',headers:{'Content-Type':'application/x-www-form-urlencoded'},body:body})
   .then(function(r){return r.json()}).then(function(j){
     btn.disabled=false;
     if(!j.ok){var t='保存失败：'+(j.error||'未知错误')+'（本次未保存任何设置）';cfgMsg(t,'warn');return;}
     cfgMsg('已保存并生效：图库 '+j.image_root+' · 缓存 '+j.cache_ttl+' 秒','ok');
     if(j.restart){
       cfgMsg('端口已改为 '+j.port+'，正在重启服务…','ok');
       if(GATEWAY){setTimeout(function(){location.reload()},1800);}
       else{var u=location.protocol+'//'+location.hostname+':'+j.port+'/';
            setTimeout(function(){location.href=u},1600);}
     }else{
       msg('');
       setTimeout(function(){location.reload()},900);
     }
   }).catch(function(e){btn.disabled=false;var t='请求失败：'+e;cfgMsg(t,'warn')});
};
document.getElementById('reload').onclick=function(){
  var btn=this;btn.disabled=true;cfgMsg('正在重新扫描图库…','');
  fetch(BASE+'/_reload',{method:'POST'})
   .then(function(r){return r.json()}).then(function(j){
     btn.disabled=false;
     if(!j.ok){cfgMsg('刷新失败：'+(j.error||'未知错误'),'warn');return;}
     cfgMsg('已重新扫描，'+(j.restart?'服务正在重启':'缓存已清空'),'ok');
     setTimeout(function(){location.reload()},900);
   }).catch(function(e){btn.disabled=false;cfgMsg('请求失败：'+e,'warn')});
};
/* 一致性体检：只读检查；按钮执行检查并点亮结果图标，点图标才展开具体问题 */
(function(){
  var btn=document.getElementById('consistency');if(!btn)return;
  var icon=document.getElementById('chkicon');
  var ASK_SVG='<svg viewBox="0 0 24 24" width="17" height="17"><rect x="3" y="3" width="18" height="18" rx="3"/><path d="M9.7 9.4a2.4 2.4 0 1 1 3.8 2c-.9.7-1.5 1.1-1.5 2.3"/><circle cx="12" cy="16.8" r=".8" fill="currentColor" stroke="none"/></svg>';
  var OK_SVG='<svg viewBox="0 0 24 24" width="17" height="17"><rect x="3" y="3" width="18" height="18" rx="3"/><path d="M7.5 12.2l3 3 6-6.4"/></svg>';
  var BAD_SVG='<svg viewBox="0 0 24 24" width="17" height="17"><rect x="3" y="3" width="18" height="18" rx="3"/><path d="M12 7.2l4.6 8.2H7.4z"/><path d="M12 10.8v2.4"/><circle cx="12" cy="15.4" r=".7" fill="currentColor" stroke="none"/></svg>';
  var detail='',cls='';
  function setIcon(state){
    if(icon){
      icon.innerHTML=state==='ok'?OK_SVG:(state==='bad'?BAD_SVG:ASK_SVG);
      icon.title=state==='ok'?'体检正常，点击查看说明':(state==='bad'?'体检异常，点击查看具体问题':'未体检，点「一致性体检」开始');
    }
    btn.className=state==='ok'?'c-ok':(state==='bad'?'c-bad':'');
  }
  setIcon('idle');
  function showDetail(){
    var e=document.getElementById('checkmsg');if(!e||!detail)return;
    e.textContent=detail;e.className='cfgmsg show '+cls;
  }
  if(icon){
    icon.onclick=function(ev){ev.stopPropagation();showDetail()};
    icon.onkeydown=function(ev){if(ev.key==='Enter'||ev.key===' '){
      ev.preventDefault();ev.stopPropagation();showDetail()}};
  }
  btn.onclick=function(){
    var b=this;b.disabled=true;
    var cm=document.getElementById('checkmsg');if(cm)cm.className='cfgmsg';
    fetch(BASE+'/_consistency')
     .then(function(r){return r.json()}).then(function(j){
       b.disabled=false;
       if(typeof r_paintOvCheck==='function')r_paintOvCheck(j);
       var nl=String.fromCharCode(10);
       if(!j.ok){detail='检查失败：'+(j.error||'未知错误');cls='warn';setIcon('bad');return;}
       var issues=[];
       if(j.in_blacklist_with_file)issues.push('有 '+j.in_blacklist_with_file+' 个已拉黑的图片仍在分类目录里（魔术师会清理）');
       if(j.recorded_no_file)issues.push('有 '+j.recorded_no_file+' 条下载记录找不到对应文件（魔术师会补拉黑并清理记录）');
       if(j.file_no_record)issues.push('有 '+j.file_no_record+' 张采集图没有下载记录（多为手动复制）');
       if(j.backup_blacklist_hits)issues.push('备份目录里有 '+j.backup_blacklist_hits+' 个已拉黑的图片（魔术师会清理）');
       if(!issues.length){detail='正常：索引、删除、拉黑三者一致。';cls='ok';setIcon('ok');return;}
       detail='不正常，发现 '+issues.length+' 项待处理：'+nl+'• '+issues.join(nl+'• ');cls='warn';setIcon('bad');
     }).catch(function(e){b.disabled=false;detail='请求失败：'+e;cls='warn';setIcon('bad')});
  };
})();
/* 概览状态卡片：一致性体检结果（只读，与设置页按钮共用 /_consistency 结果） */
function r_paintOvCheck(j){
  var e=document.getElementById('ovCheck');if(!e)return;
  if(!j||!j.ok){e.className='v warn';e.textContent='检查失败';return;}
  var n=(j.in_blacklist_with_file||0)+(j.recorded_no_file||0)
       +(j.file_no_record||0)+(j.backup_blacklist_hits||0);
  if(!n){e.className='v ok';e.textContent='正常';}
  else{e.className='v warn';e.textContent=n+' 项待处理';}
}
(function(){
  var e=document.getElementById('ovCheck');if(!e)return;
  fetch(BASE+'/_consistency',{cache:'no-store'})
   .then(function(r){return r.json()}).then(r_paintOvCheck)
   .catch(function(){r_paintOvCheck(null)});
})();
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
  if(el){el.className='keydot'+(apiKeySet?' on':'');
    el.title=apiKeySet?'已设置 · 可选 Sketchy / NSFW':'未设置 · 仅 SFW';}
  var ov=document.getElementById('ovKey');
  if(ov){ov.textContent=apiKeySet?'已设置':'未设置';ov.className='v '+(apiKeySet?'ok':'warn');}
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
  var cnt=parseInt(val('t_count'),10);
  if(isNaN(cnt)||cnt<1)cnt=24;
  if(cnt>480)cnt=480;
  return {type:'fetch',target:val('t_target'),count:cnt,
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
var TSTATUS={'idle':'就绪','running':'采集中','stopping':'正在停止…','done':'已完成',
  'error':'失败','cancelled':'已停止','empty':'无匹配图'};
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
    var stopping=t.running&&t.phase==='stopping';
    var st=t.running?(stopping?'正在停止…':'运行中'):(TSTATUS[t.phase]||TSTATUS[t.last_status]||t.last_status||'就绪');
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
    h+='<button data-act="stop" data-id="'+esc(t.id)+'"'+((t.running&&!stopping)?'':' disabled')+'>'+(stopping?'停止中…':'停止')+'</button>';
    h+='<button data-act="edit" data-id="'+esc(t.id)+'">编辑</button>';
    h+='<button data-act="log" data-id="'+esc(t.id)+'">日志</button>';
    h+='<button data-act="delete" data-id="'+esc(t.id)+'">删除</button>';
    h+='</div></div>';
  }
  box.innerHTML=h;
}
/* ---- image compression tasks (share the same task queue & scheduler) ---- */
var ZSTATUS={'idle':'就绪','running':'压缩中','stopping':'正在停止…','done':'已完成',
  'error':'失败','cancelled':'已停止','empty':'无需要处理'};
function zcfgLabel(cfg){
  cfg=cfg||{};var r=[];
  r.push('短边≤'+(cfg.max_height?cfg.max_height:'不限'));
  r.push('体积≤'+(cfg.max_size_mb?cfg.max_size_mb+'MB':'不限'));
  r.push('质量'+(cfg.q_min||85)+'-'+(cfg.q_max||98));
  r.push(cfg.to_jpg?'转JPG':'仅压JPG');
  if(cfg.recursive)r.push('含子目录');
  if(cfg.full_backup)r.push('全量备份');
  return r.join(' · ');
}
function renderZipTasks(tasks,now){
  var box=document.getElementById('zlist');
  tasks=tasks.filter(function(t){return t.type==='compress';});
  if(!tasks.length){box.innerHTML='<p class="meta">还没有压缩任务，点下方「新建压缩任务」开始。</p>';return;}
  var h='';
  for(var i=0;i<tasks.length;i++){
    var t=tasks[i];
    var stopping=t.running&&t.phase==='stopping';
    var st=t.running?(stopping?'正在停止…':'运行中'):(ZSTATUS[t.phase]||ZSTATUS[t.last_status]||t.last_status||'就绪');
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
    h+='<button data-act="stop" data-id="'+esc(t.id)+'"'+((t.running&&!stopping)?'':' disabled')+'>'+(stopping?'停止中…':'停止')+'</button>';
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
    recursive:document.getElementById('z_rec').checked?'1':'0',
    full_backup:document.getElementById('z_fullbackup').checked?'1':'0'};
}
function zFillForm(cfg){
  var map={z_src:'src_dir',z_backup:'backup_dir',z_height:'max_height',
    z_size:'max_size_mb',z_qmax:'q_max',z_qmin:'q_min'};
  for(var id in map){if(Object.prototype.hasOwnProperty.call(map,id)){
    var el=document.getElementById(id);if(el)el.value=cfg[map[id]]==null?'':cfg[map[id]];}}
  document.getElementById('z_tojpg').checked=String(cfg.to_jpg)!=='0';
  document.getElementById('z_rec').checked=String(cfg.recursive)==='1';
  document.getElementById('z_fullbackup').checked=String(cfg.full_backup)==='1';
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
        theme=cfg["theme"],
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
        cupchecked=" checked" if cfg.get("cleanup_uploads") else "",
        cleanupuploads="true" if cfg.get("cleanup_uploads") else "false",
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
        theme = cfg["theme"]  # 主题由各设备本地保存，配置保存不再改动它
        cleanup_uploads = 1 if val("cleanup_uploads") in ("1", "true", "on", "yes") else 0
        if port != old_port:
            s = socket.socket()
            try:
                s.bind(("0.0.0.0", port))
            except OSError:
                return self.send_json({"ok": False,
                                       "error": "端口 %d 已被占用，请换一个" % port}, 409)
            finally:
                s.close()
        new = {"image_root": root, "port": port, "cache_ttl": ttl, "theme": theme,
               "cleanup_uploads": cleanup_uploads}
        try:
            save_config(new)
        except OSError as exc:
            return self.send_json({"ok": False, "error": "配置写入失败：%s" % exc}, 500)
        _cache["ts"] = 0.0
        restart = port != old_port
        log("config saved: port=%d root=%s ttl=%d theme=%s restart=%s"
            % (port, root or "(default share)", ttl, theme, restart))
        if restart:
            schedule_execv()
        return self.send_json({
            "ok": True, "port": port,
            "image_root": root or detect_share(),
            "cache_ttl": ttl, "restart": restart,
            "message": "端口已修改，服务正在重启" if restart else "配置已保存并立即生效",
        })

    def handle_theme(self, form):
        theme = valid_theme((form.get("theme") or [""])[0].strip())
        cfg = load_config()
        cfg["theme"] = theme
        try:
            save_config(cfg)
        except OSError as exc:
            return self.send_json({"ok": False, "error": "主题保存失败：%s" % exc}, 500)
        return self.send_json({"ok": True, "theme": theme})

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
        cat = self._form_val(form, "cat")
        if any_task_running():
            return self.send_json(
                {"ok": False, "error": "有采集/压缩任务正在运行，请等任务结束后再执行魔术师"},
                409)
        ok, payload = sweep_missing_blacklist()
        if not ok:
            return self.send_json({"ok": False, "error": payload}, 400)
        sweep_records = payload.get("records_removed", 0)
        # 第二步：全局删除所有分类和备份目录里 ID 已进黑名单的采集图
        ok2, purged = purge_blacklisted_everywhere(cat)
        if not ok2:
            return self.send_json({"ok": False, "error": purged}, 400)
        payload.update(purged)
        payload["records_removed"] = sweep_records + purged.get("records_removed", 0)
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
        _task_queue.put((tid, False))
        return self.send_json({"ok": True})

    def handle_tasks_stop(self, form):
        tid = self._form_val(form, "id")
        with _tasks_lock:
            rt = _task_rt.get(tid)
            if not rt or not rt["running"]:
                return self.send_json({"ok": False, "error": "该任务未在运行"}, 409)
            already_stopping = rt.get("phase") == "stopping"
            rt["cancel"].set()
            if not already_stopping:
                rt["phase"] = "stopping"
                rt["log"].append("已请求停止，正在中断当前操作…")
                if len(rt["log"]) > 80:
                    del rt["log"][:len(rt["log"]) - 80]
            resp = rt.get("_resp")          # active blocking read, if any
            proc = rt.get("_proc")          # active ffmpeg / ffprobe, if any
        # Closing the socket makes a stalled resp.read() return immediately;
        # wh_request's chunk loop then sees the cancel flag and raises.
        if resp is not None:
            try:
                resp.close()
            except Exception:
                pass
        # Terminating the running image tool makes a stalled communicate()
        # return; _run_tool then sees the cancel flag and raises. The work
        # file lives in tmpdir and is removed in compress_images' finally,
        # so no partially-written image reaches the destination.
        if proc is not None:
            try:
                proc.terminate()
            except Exception:
                pass
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
        if path == "/_consistency":
            return self.send_json(consistency_check())
        if path == "/_preview_label":
            q = parse_qs(urlparse(self.path).query)
            cat = q.get("cat", [""])[0]
            try:
                idx = int(q.get("i", ["0"])[0])
            except (ValueError, IndexError):
                idx = 0
            return self.send_json({"ok": True, "label": preview_image_label(cat, idx)})
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
            if path == "/_theme":
                return self.handle_theme(form)
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
