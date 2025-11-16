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
- `LINK`：存放要爬取友链页面的 URL 列表
- `link_page_rules`：CSS 选择器规则，用于提取友链页面中的姓名/链接/头像
- `SETTINGS_FRIENDS_LINKS`：手动友链列表，格式为 `[name, url, avatar, optional_feed_suffix]`；若填写了 `feed_suffix`，程序会直接用拼接后的 URL 去尝试抓取（可绕过自动发现逻辑）
- `BLOCK_SITE` / `BLOCK_SITE_REVERSE`：黑/白名单规则（支持正则）
- `feed_suffix`：默认尝试的一组常见后缀
- `MAX_POSTS_NUM`：每站点最多保留的帖子数（0 表示不限制）
- `OUTDATE_CLEAN`：过期清理天数，设为 `0` 表示不限制（保留所有历史文章）
- `TIMEZONE_CORRECTION`：是否进行时区转换（默认 `true`）
  - `true`：把 RSS 时间换算为北京时间（UTC+8）
  - `false`：不做换算，保留对方文章的“墙上时间”，仅以北京时间标注（+08:00）
  - 示例：
    - `<pubDate>Sat, 15 Nov 2025 14:41:01 GMT</pubDate>` →
      - `true`: `2025-11-15T22:41:01+08:00`
      - `false`: `2025-11-15T14:41:01+08:00`
    - `<pubDate>Fri, 14 Nov 2025 23:23:25 +0800</pubDate>` →
      - `true/false` 均为 `2025-11-14T23:23:25+08:00`
- `OUTPUT_JSON_FILENAME`：输出文件名，例：`rss.json`（默认 `data.json`）

输出格式（默认 `data.json`）— 重要字段说明

主要结构：

```json
{
  "updated_at": "2025-11-14T22:08:12.876043",
  "total_sites": 22,
  "total_posts": 199,
  "sites": [
    {
      "name": "站点名称",
      "url": "https://example.com/",
      "avatar": "https://example.com/avatar.png",
      "feed_url": "https://example.com/feed",
      "posts": [
        {
          "title": "文章标题",
          "link": "https://example.com/article",
          "description": "文章摘要",
          "pub_date": "2025-11-14T10:00:00",
          "updated_at": "2025-11-14T10:00:00",
          "author": "作者",
          "site_name": "站点名称",
          "site_url": "https://example.com/",
          "avatar": "https://example.com/avatar.png"
        }
      ]
    }
  ],
  "all_posts": [ /* 按时间倒序的所有文章 */ ],
  "failed_sites": [ /* 获取失败的站点清单 */
    { "name": "站点名称", "url": "https://example.com/", "feed_url": "https://example.com/feed", "reason": "HTTP 520" }
  ]
}
```

关于 `failed_sites`
- 程序会把“未找到 feed”或“尝试抓取 feed 失败（如 HTTP 错误、超时、解析异常）”的站点记录到 `failed_sites`，包含 `reason` 字段，便于后续排查或人工干预（例如把真实 feed 写入配置）。

在 GitHub 上自动化运行
- 项目包含一个 Actions workflow（`.github/workflows/main.yml`），示例设为每 6 小时运行一次。若你自定义了输出文件名（如 `rss.json`），请相应更新工作流中对输出文件的引用（默认示例使用 `data.json`）。



