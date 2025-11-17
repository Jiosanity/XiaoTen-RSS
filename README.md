# 小十友圈RSS聚合工具

这是一个轻量的 RSS 聚合工具，它会从「友链页面」与配置的手动友链中发现 RSS/Atom 源，抓取并聚合文章，最终输出为由 `OUTPUT_JSON_FILENAME` 指定的 JSON 文件（默认 `data.json`），可供前端或静态站点使用。

核心功能（最新）
- 从友链页面按 CSS 规则自动提取站点链接
- 支持手动添加友链并可配置自定义 feed 后缀（如 `rss`、`rss.xml` 等）
- 自动发现并验证常见 Feed 后缀
- 黑名单 / 白名单站点过滤
- 支持不限制过期文章（`OUTDATE_CLEAN: 0` 表示不过滤）
- 为每篇文章提供发布时间 `pub_date` 与更新时间 `updated_at`
- 在最终输出中包含抓取失败的站点列表 `failed_sites`（含失败原因）
- 支持 GitHub Actions 定时运行（例如每 6 小时）

最小文件清单（保留）
- `main.py` — 主程序
- `setting.yaml` — 配置
- `requirements.txt` — 依赖
- `README.md` — 本说明（你现在正在查看）
- 输出 JSON（默认 `data.json`，可通过 `OUTPUT_JSON_FILENAME` 自定义）

快速使用
1. 克隆并进入仓库

```powershell
git clone <your-repo-url>
cd xiaoten-rss
```

2. 安装依赖

```powershell
pip install -r requirements.txt
```

3. 运行聚合

```powershell
python main.py
```

程序运行结束后会在仓库根目录写入或更新输出 JSON（默认 `data.json`，可在 `setting.yaml` 的 `OUTPUT_JSON_FILENAME` 中自定义，例如 `rss.json`）。

配置要点（`setting.yaml`）

## 基础配置（速览）
- `LINK`：友链页面 URL 列表
- `link_page_rules`：从友链页提取 姓名/链接/头像 的 CSS 规则
- `SETTINGS_FRIENDS_LINKS`：手动友链 `[name, url, avatar, optional_feed_suffix]`
- `BLOCK_SITE` / `BLOCK_SITE_REVERSE`：黑/白名单（正则）
- `feed_suffix`：常见 Feed 后缀尝试顺序
- `MAX_POSTS_NUM`：每站最多文章数（0 不限）
- `OUTDATE_CLEAN`：过期清理天数（≤0 表示不过滤）
- `TIMEZONE_CORRECTION`：是否换算为北京时间（`true` 换算；`false` 保留来源显示的时间但标注 +08:00）
- `SORT_BY`：排序字段（`pub_date` 或 `updated_at`）
- `OUTPUT_JSON_FILENAME`：输出文件名（如 `rss.json`，默认 `data.json`）

## 手动配置覆盖策略

- 有 `feed_suffix`：当手动友链为同一 `url` 指定了 `feed_suffix`，将直接采用拼接后的地址（覆盖已从友链页自动发现的 `feed_url`）。
- 无 `feed_suffix` 且 URL 已存在：跳过该手动项，保留自动发现结果（避免重复）。
- 无 `feed_suffix` 且 URL 不存在：按常见后缀（`feed`、`rss`、`atom.xml`、`index.xml`、`rss.xml`）尝试自动发现。
- 黑名单不影响手动项：`BLOCK_SITE` 仅作用于友链页面爬取，手动配置的站点不受其限制。

## 高级配置（性能优化）
- `LOG_LEVEL`：日志级别（DEBUG, INFO, WARNING, ERROR），默认 INFO
- `MAX_WORKERS`：并发处理友链的线程数，0 或负数表示串行处理，建议 4-8（默认 4）
- `REQUEST_TIMEOUT`：HTTP 请求超时时间（秒），默认 10
- `FEED_CHECK_TIMEOUT`：Feed URL 检查超时时间（秒），默认 5
- `REQUEST_RETRIES`：HTTP 请求重试次数，默认 1
- `RETRY_BACKOFF`：重试退避系数（秒），默认 0.3

输出格式（默认 `data.json`）— 速览

- 顶层：`updated_at`、`total_sites`、`total_posts`、`sites[]`、`all_posts[]`、`failed_sites[]`
- `sites[i]`：`name`、`url`、`avatar`、`feed_url`、`posts[]`
- `sites[i].posts[j]`：`title`、`link`、`description`、`pub_date`、`updated_at`、`author`
- `all_posts[k]`：为所有文章的扁平列表，包含上面字段，且附带 `site_name`、`site_url`、`avatar`
- `failed_sites[m]`：抓取失败站点清单，含 `name`、`url`、`feed_url`（如有）与 `reason`

在 GitHub 上自动化运行
- 项目包含一个 Actions workflow（`.github/workflows/main.yml`），示例设为每 6 小时运行一次。若你自定义了输出文件名（如 `rss.json`），请相应更新工作流中对输出文件的引用（默认示例使用 `data.json`）。
 

## 更新日志

### 2025-11-17
- **优化手动配置优先级逻辑**：手动配置的友链不再受黑名单限制，优先级更高
- **支持自定义RSS后缀覆盖**：当手动配置中指定了自定义 `feed_suffix` 时，即使该站点已从友链页面抓取，也会使用手动配置的RSS地址覆盖
- **修复特殊RSS路径获取问题**：解决了如 `rss.php`、`article/rss.xml` 等非标准后缀的RSS源无法获取的问题
- **移除rss.json追踪**：将自动生成的 `rss.json` 从版本控制中移除，避免不必要的提交



