# RanPix

一个轻量、零依赖的随机图片 API 应用，原生运行于[飞牛 OS（fnOS）](https://www.fnnas.com/)。

图库根目录下的**每个一级子文件夹自动成为一个独立的随机图片接口**。例如放入 `anime/` 和 `wallpaper/` 两个文件夹，访问 `/anime` 与 `/wallpaper` 就会各自随机返回一张图片。多个接口互不影响，随取随换。

## 特性

- **原生 fpk 包**：直接在飞牛应用中心安装，不需要 Docker，不依赖第三方 Python 库（仅用标准库）。
- **多接口**：每个一级子文件夹即一个 API，接口名大小写不敏感。
- **两种访问方式**：
  - 直连端口 `http://<NAS-IP>:<端口>/<接口名>`，适合局域网和第三方调用；
  - 飞牛同源网关 `https://<NAS>/app/ranpix/<接口名>`，桌面图标与手机 App 入口走这里，外网 / HTTPS 也能打开。
- **可自定义**：服务端口、图片根目录、目录清单缓存秒数都能在设置页修改。
- **不缓存图片**：响应带 `Cache-Control: no-store`，每次请求都是新的一张。
- **管理页**：内置接口列表、`/_health` 健康检查、`/_apis` 接口清单、一键刷新。

## 截图

管理页在手机端的预览：

![RanPix 移动端预览](ranpix-mobile-preview.png)

## 安装

1. 从 [最新 Release](https://github.com/le5inioo/ranpix/releases/latest) 下载 `ranpix.fpk`（或直接使用仓库根目录的 `ranpix.fpk`）。
2. 飞牛 OS → 应用中心 → 右上角菜单 → 安装本地包，选择 `ranpix.fpk`。
3. 安装向导里可设置：
   - **服务端口**：默认 `18580`，改成未被占用的端口；
   - **图片根目录**：留空则用应用自带共享目录 `/vol1/@appshare/ranpix`；也可填 NAS 上已有文件夹的绝对路径，例如 `/vol1/1000/Pictures`。
4. 安装后启动应用，桌面会出现 RanPix 图标，点开即管理页。

### 关于目录权限

应用以专用用户运行，只授权了顶层共享文件夹。如果图片放在自定义目录：

- **顶层文件夹**：到「设置 → 应用管理 → RanPix → 权限设置」授权该文件夹；
- **子文件夹**：应用权限列表不包含子目录，需到「文件管理 → 详细信息 → 权限 → 高级」启用**继承父级权限**，否则应用读不到图片，对应接口会显示 0 张。

## 使用

准备图库，例如把图片放进图库根目录下的 `anime/` 和 `wallpaper/`：

```
/vol1/1000/Pictures/
├── anime/        → 接口 /anime
├── wallpaper/    → 接口 /wallpaper
└── 手机壁纸/      → 接口 /手机壁纸
```

然后随机取图：

```
# 局域网直连（端口在安装时设置，默认 18580）
http://192.168.1.10:18580/anime
http://192.168.1.10:18580/wallpaper

# 飞牛同源网关（外网 / HTTPS 也可用）
https://your-nas.example.com/app/ranpix/anime
```

接口名大小写不敏感，`/wallpaper`、`/Wallpaper` 都能命中同名文件夹。

辅助端点：

| 路径 | 说明 |
| --- | --- |
| `/` | 管理页，列出所有接口、图片数、复制地址 |
| `/_apis` | JSON 接口清单与图片数量 |
| `/_health` | 健康检查与运行状态 |
| `/_icon` | 应用图标 |

## 配置

安装向导、应用设置页、管理页三处都可修改，配置保存在 `TRIM_PKGETC/config.json`：

| 字段 | 默认 | 说明 |
| --- | --- | --- |
| `image_root` | 空（用应用共享目录） | 图库根目录绝对路径 |
| `port` | `18580` | 直连服务端口 |
| `cache_ttl` | `30` | 目录清单缓存秒数，见下 |

**缓存秒数**缓存的是扫描图库得到的**图片清单**，不是图片本身，也不影响 `/anime` 每次随机返回不同图片（响应始终是 `no-store`）。它只决定：新建子文件夹、增删图片后，多久才会在接口列表和计数里体现。图库大且不常改动可调大以省磁盘扫描；保存设置或管理页点「立即刷新」会立即清空缓存。

## 从源码构建

仓库 `fpk/` 目录是完整的打包源。飞牛应用包需用系统自带的 `fnpack` 生成，建议在 NAS 上构建：

```bash
# 在 NAS 上，把 fpk/ 目录放到 /tmp/fpkbuild/ranpix/
cd /tmp/fpkbuild
fnpack build ranpix           # 生成 /tmp/fpkbuild/ranpix.fpk
```

源码结构：

```
fpk/
├── manifest              # 应用清单
├── ICON.PNG / ICON_256.PNG
├── app/
│   ├── server.py         # 全部服务端逻辑（标准库实现）
│   └── ui/
│       ├── config        # 桌面/手机 App 入口配置
│       └── images/       # 三档图标
├── cmd/                  # 生命周期与配置回调脚本
├── config/               # 权限与资源声明
└── wizard/               # 安装/设置向导
```

## 致谢

灵感来自 [wscck/Random-Image-API](https://github.com/wscck/Random-Image-API)，本实现为面向飞牛 OS 的原生重写，不依赖原项目的 Flask/Docker 方案。

## 许可证

[MIT](LICENSE) © le5inioo
