# RanPix

飞牛 OS（fnOS）原生的随机图片 API，零第三方依赖（仅 Python 标准库），fpk 包直接安装，无需 Docker。

图库根目录下每个一级子文件夹自动成为一个独立接口：放入 `anime/`、`wallpaper/`，访问 `/anime`、`/wallpaper` 即各自随机返回一张图，互不影响。

## 特性

- **多接口**：每个一级子文件夹即一个 API，名称大小写不敏感。
- **双入口**：直连 `http://<NAS-IP>:<端口>/<接口名>`（局域网 / 第三方调用）；同源网关 `https://<NAS>/app/ranpix/<接口名>`（桌面 / 手机 App / 外网 HTTPS）。
- **Wallhaven 采集**：多任务、周几定时、页码与分类/纯净度/比例/排序筛选、API Key、顺序下载、黑名单去重。
- **图片压缩**：定时批量压缩，短边 PX + 质量设置、备份原图，用系统 ffmpeg。
- **预览与拉黑**：「打开看看」按下载时间浏览，删除即加入黑名单，后续采集自动跳过。
- **不缓存图片**：响应 `no-store`，每次请求都是新的一张。

## 安装

1. 下载最新 [Release](https://github.com/le5inioo/ranpix/releases/latest) 的 `ranpix.fpk`。
2. 飞牛 OS → 应用中心 → 右上角菜单 → 安装本地包，选择 `ranpix.fpk`。
3. 向导中设置端口（默认 `18580`）与图片根目录（留空用 `/vol1/@appshare/ranpix`）。
4. 启动后桌面出现图标，点开即管理页。

自定义目录需授权：顶层文件夹在「设置 → 应用管理 → RanPix → 权限设置」授权；子文件夹在「文件管理 → 详细信息 → 权限 → 高级」开启继承父级权限，否则接口显示 0 张。

## 使用

```
/vol1/1000/Pictures/
├── anime/      → /anime
├── wallpaper/  → /wallpaper
└── 手机壁纸/    → /手机壁纸
```

```
http://192.168.1.10:18580/anime                  # 直连
https://your-nas.example.com/app/ranpix/anime    # 网关
```

接口名大小写不敏感。辅助端点：`/` 管理页 · `/_apis` 接口清单 · `/_health` 健康检查 · `/_icon` 图标。

## 配置

向导、设置页、管理页均可改，保存在 `TRIM_PKGETC/config.json`：

| 字段 | 默认 | 说明 |
| --- | --- | --- |
| `image_root` | 空 | 图库根目录绝对路径，空则用应用共享目录 |
| `port` | `18580` | 直连端口 |
| `cache_ttl` | `30` | 图库清单缓存秒数 |

## 构建

`fpk/` 是完整打包源，用飞牛自带 `fnpack` 在 NAS 上构建：

```bash
fnpack build ranpix    # 生成 ranpix.fpk
```

## 许可证

[MIT](LICENSE) © le5inioo
