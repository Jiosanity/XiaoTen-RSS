#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
友链RSS订阅聚合程序
从友链页面和手动配置列表中获取RSS源，聚合成可配置的JSON文件
"""

import os
import json
import re
import logging
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from typing import List, Dict, Any, Tuple, Optional
from urllib.parse import urljoin, urlparse, parse_qs, unquote
import hashlib
from time import sleep
from concurrent.futures import ThreadPoolExecutor, as_completed

import requests
import yaml
from bs4 import BeautifulSoup
import feedparser
from requests.adapters import HTTPAdapter
from urllib3.util import Retry
import urllib3

try:
    from playwright.sync_api import sync_playwright
    PLAYWRIGHT_AVAILABLE = True
except ImportError:
    PLAYWRIGHT_AVAILABLE = False

# 禁用SSL警告
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# 初始化logger（稍后会根据配置设置级别）
logger = logging.getLogger(__name__)

# 定义北京时间时区 (UTC+8)
BEIJING_TZ = timezone(timedelta(hours=8))

# 默认配置（可被 setting.yaml 覆盖）
DEFAULT_CONFIG = {
    'REQUEST_TIMEOUT': 10,
    'FEED_CHECK_TIMEOUT': 5,
    'REQUEST_RETRIES': 1,
    'RETRY_BACKOFF': 0.3,
    'MAX_WORKERS': 0,  # 0 表示不使用并发
    'LOG_LEVEL': 'INFO',
    'CACHE_FILE': 'feed_cache.json',
    'STALE_FALLBACK_ENABLED': True,
    'STALE_FALLBACK_INCLUDE_MISSING_SITES': True,
    'MIN_SITE_RETENTION_RATIO': 0.8,
    'MIN_POST_RETENTION_RATIO': 0.7,
    'MAX_FAILED_SITES_FOR_PUBLISH': 10,
    'USER_AGENT': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
}

def get_beijing_time():
    """获取当前北京时间"""
    return datetime.now(BEIJING_TZ)


def normalize_site_url(url: str) -> str:
    """规范化站点 URL，用于跨运行匹配同一友链。"""
    return (url or '').strip().rstrip('/')

def parse_feed_time(time_tuple, timezone_correction: bool = True, original_time_str: Optional[str] = None):
    """解析feed时间
    
    Args:
        time_tuple: feedparser解析的时间元组（通常为UTC）
        timezone_correction: 是否进行时区校正（True: 转为北京时间；False: 保留对方文章的“墙上时间”并标注为北京时间）
        original_time_str: 原始时间字符串（如 RFC822 的 pubDate），用于在关闭校正时准确保留墙上时间
    Returns:
        datetime: 带时区信息的时间
    """
    # 关闭校正：尽量使用原始字符串来保留“墙上时间”
    if not timezone_correction and original_time_str:
        try:
            dt = parsedate_to_datetime(original_time_str)
            # 保留对方文章的墙上时间（几点就是几点），但标注为北京时间
            # 无论原本属于哪个时区，都只取出时分秒与日期，不做换算
            local_dt = datetime(dt.year, dt.month, dt.day, dt.hour, dt.minute, dt.second, tzinfo=BEIJING_TZ)
            return local_dt
        except Exception as e:
            logger.debug(f"解析原始时间字符串失败，回退到元组处理: {e}")
            # 继续走下面的 time_tuple 逻辑
    
    if not time_tuple:
        # 没有任何时间可用，使用当前北京时间
        return get_beijing_time()
    
    try:
        # feedparser 的时间元组通常是按 UTC 提供
        utc_dt = datetime(*time_tuple[:6], tzinfo=timezone.utc)
        if timezone_correction:
            # 开启校正：将 UTC 转为北京时间
            return utc_dt.astimezone(BEIJING_TZ)
        else:
            # 关闭校正：保留墙上时间——用 UTC 的时分秒直接标注为北京时间
            # 注意：当缺失原始字符串时，无法还原原时区的墙上时间，只能使用UTC墙上时间
            wall_dt = datetime(utc_dt.year, utc_dt.month, utc_dt.day, utc_dt.hour, utc_dt.minute, utc_dt.second, tzinfo=BEIJING_TZ)
            return wall_dt
    except Exception as e:
        logger.warning(f"时间解析失败: {e}, 使用当前时间代替")
        return get_beijing_time()


class CacheManager:
    """缓存管理器，存储已发现的RSS源和文章ID"""
    
    def __init__(self, cache_file: str = 'feed_cache.json'):
        self.cache_file = cache_file
        self.cache = self._load_cache()
    
    def _load_cache(self) -> dict:
        """加载缓存"""
        if os.path.exists(self.cache_file):
            try:
                with open(self.cache_file, 'r', encoding='utf-8') as f:
                    cache_data = json.load(f)
                    # 移除旧版本可能存在的 article_ids
                    cache_data.pop('article_ids', None)
                    return cache_data
            except Exception as e:
                logger.warning(f"加载缓存失败: {e}")
                return self._init_cache()
        return self._init_cache()
    
    def _init_cache(self) -> dict:
        """初始化缓存结构"""
        return {
            'feed_urls': {},  # {site_url: feed_url}
            'last_update': None
        }
    
    def save(self):
        """保存缓存"""
        try:
            with open(self.cache_file, 'w', encoding='utf-8') as f:
                json.dump(self.cache, f, ensure_ascii=False, indent=2)
            logger.debug(f"缓存已保存")
        except Exception as e:
            logger.error(f"保存缓存失败: {e}")
    
    def get_cached_feed_url(self, site_url: str) -> Optional[str]:
        """获取缓存的Feed URL"""
        return self.cache.get('feed_urls', {}).get(site_url)
    
    def set_feed_url(self, site_url: str, feed_url: str):
        """缓存Feed URL"""
        if 'feed_urls' not in self.cache:
            self.cache['feed_urls'] = {}
        self.cache['feed_urls'][site_url] = feed_url


class ConfigParser:
    """解析setting.yaml配置文件"""
    
    def __init__(self, config_path: str = 'setting.yaml'):
        self.config_path = config_path
        self.config = self._load_config()
        self._setup_logging()
    
    def _load_config(self) -> dict:
        """加载YAML配置文件"""
        with open(self.config_path, 'r', encoding='utf-8') as f:
            return yaml.safe_load(f)
    
    def _setup_logging(self):
        """配置日志系统"""
        log_level = self.get_log_level()
        logging.basicConfig(
            level=getattr(logging, log_level),
            format='%(asctime)s - %(levelname)s - %(message)s',
            force=True  # 强制重新配置
        )
    
    def get_link_pages(self) -> List[Dict[str, Any]]:
        """获取需要爬取的友链页面配置列表
        
        每项包含:
          - link: 页面 URL（必须）
          - js_render: 是否使用 JS 渲染（可选）
          - wait_selector: 等待的选择器（可选）
        """
        pages = []
        for item in self.config.get('LINK', []):
            if isinstance(item, dict) and 'link' in item:
                pages.append(item)
        return pages
    
    def get_link_page_rules(self) -> dict:
        """获取CSS选择器规则"""
        return self.config.get('link_page_rules', {})
    
    def get_block_sites(self) -> List[str]:
        """获取屏蔽站点列表"""
        return self.config.get('BLOCK_SITE', [])
    
    def get_block_site_reverse(self) -> bool:
        """获取是否使用白名单模式"""
        return self.config.get('BLOCK_SITE_REVERSE', False)
    
    def get_manual_links(self) -> List[Dict[str, str]]:
        """获取手动添加的友链列表"""
        manual_links = []
        links_list = self.config.get('SETTINGS_FRIENDS_LINKS', {}).get('list', [])
        
        for item in links_list:
            if isinstance(item, list) and len(item) >= 3:
                link_dict = {
                    'name': item[0],
                    'url': item[1],
                    'avatar': item[2],
                    'feed_suffix': item[3] if len(item) > 3 else None
                }
                manual_links.append(link_dict)
        return manual_links
    
    def get_feed_suffixes(self) -> List[str]:
        """获取Feed后缀列表"""
        return self.config.get('feed_suffix', [])
    
    def get_max_posts(self) -> int:
        """获取每个站点最多抓取文章数"""
        return self.config.get('MAX_POSTS_NUM', 5)
    
    def get_outdate_days(self) -> int:
        """获取过期文章天数
        
        Returns:
            int: 过期天数，0或负数表示不限制
        """
        return self.config.get('OUTDATE_CLEAN', 180)

    def get_timezone_correction(self) -> bool:
        """获取是否开启时区校正
        
        Returns:
            bool: True - 将所有时间换算为北京时间
                  False - 不换算，保留对方文章的墙上时间，仅以北京时间标注
        """
        return self.config.get('TIMEZONE_CORRECTION', True)

    def get_sort_by(self) -> str:
        """获取文章排序方式
        
        Returns:
            str: 'pub_date' - 按发布时间排序（默认）
                 'updated_at' - 按更新时间排序
        """
        sort_by = self.config.get('SORT_BY', 'pub_date')
        if sort_by not in ['pub_date', 'updated_at']:
            logger.warning(f"无效的排序方式: {sort_by}，使用默认值 pub_date")
            return 'pub_date'
        return sort_by

    def get_output_filename(self) -> str:
        """获取输出JSON文件名
        
        Returns:
            str: 输出文件名（相对仓库根目录），默认 'data.json'
        """
        return self.config.get('OUTPUT_JSON_FILENAME', 'data.json')
    
    def get_log_level(self) -> str:
        """获取日志级别"""
        return self.config.get('LOG_LEVEL', 'INFO').upper()
    
    def get_max_workers(self) -> int:
        """获取并发处理线程数"""
        return self.config.get('MAX_WORKERS', 0)
    
    def get_request_timeout(self) -> int:
        """获取HTTP请求超时时间"""
        return self.config.get('REQUEST_TIMEOUT', 10)
    
    def get_feed_check_timeout(self) -> int:
        """获取Feed URL检查超时时间"""
        return self.config.get('FEED_CHECK_TIMEOUT', 5)
    
    def get_request_retries(self) -> int:
        """获取HTTP请求重试次数"""
        return self.config.get('REQUEST_RETRIES', 1)
    
    def get_retry_backoff(self) -> float:
        """获取重试退避系数"""
        return self.config.get('RETRY_BACKOFF', 0.3)
    
    def get_cache_file(self) -> str:
        """获取缓存文件名"""
        return self.config.get('CACHE_FILE', 'feed_cache.json')
    
    def get_user_agent(self) -> str:
        """获取User-Agent"""
        return self.config.get('USER_AGENT', DEFAULT_CONFIG['USER_AGENT'])

    def get_stale_fallback_enabled(self) -> bool:
        """是否启用上一版输出兜底。"""
        return self.config.get('STALE_FALLBACK_ENABLED', DEFAULT_CONFIG['STALE_FALLBACK_ENABLED'])

    def get_stale_fallback_include_missing_sites(self) -> bool:
        """是否补回本轮未出现在友链列表中的旧站点。"""
        return self.config.get(
            'STALE_FALLBACK_INCLUDE_MISSING_SITES',
            DEFAULT_CONFIG['STALE_FALLBACK_INCLUDE_MISSING_SITES']
        )

    def get_min_site_retention_ratio(self) -> float:
        """获取站点数发布门禁比例。"""
        return float(self.config.get('MIN_SITE_RETENTION_RATIO', DEFAULT_CONFIG['MIN_SITE_RETENTION_RATIO']))

    def get_min_post_retention_ratio(self) -> float:
        """获取文章数发布门禁比例。"""
        return float(self.config.get('MIN_POST_RETENTION_RATIO', DEFAULT_CONFIG['MIN_POST_RETENTION_RATIO']))

    def get_max_failed_sites_for_publish(self) -> int:
        """获取允许发布的最大失败站点数。"""
        return int(self.config.get('MAX_FAILED_SITES_FOR_PUBLISH', DEFAULT_CONFIG['MAX_FAILED_SITES_FOR_PUBLISH']))


class SiteFilter:
    """站点过滤器，处理黑/白名单"""
    
    def __init__(self, block_sites: List[str], reverse: bool = False):
        self.block_sites = block_sites
        self.reverse = reverse
    
    def is_blocked(self, url: str) -> bool:
        """检查URL是否被屏蔽
        
        黑名单模式 (reverse=False): 匹配的被屏蔽，其他允许
        白名单模式 (reverse=True): 匹配的被允许，其他屏蔽
        """
        for pattern in self.block_sites:
            if re.search(pattern, url):
                # 匹配到规则
                # 黑名单模式: 匹配的被屏蔽
                if not self.reverse:
                    return True
                # 白名单模式: 匹配的被允许
                else:
                    return False
        
        # 未匹配到规则
        # 黑名单模式: 未匹配的允许
        if not self.reverse:
            return False
        # 白名单模式: 未匹配的屏蔽
        else:
            return True


class LinkPageScraper:
    """友链页面爬虫"""
    
    def __init__(self, rules: dict, request_timeout: int = 10, user_agent: str = None):
        self.rules = rules
        self.request_timeout = request_timeout
        self.user_agent = user_agent or DEFAULT_CONFIG['USER_AGENT']
        self.session = self._create_session()
    
    def _create_session(self) -> requests.Session:
        """创建带重试机制的requests会话"""
        session = requests.Session()
        session.headers.update({'User-Agent': self.user_agent})
        session.verify = False
        return session
    
    def scrape(self, page_config) -> List[Dict[str, str]]:
        """从友链数据源获取链接"""
        if isinstance(page_config, str):
            page_config = {'link': page_config}
        
        url = page_config.get('link', '')
        if not url:
            return []
            
        js_render = page_config.get('js_render', False)
        wait_selector = page_config.get('wait_selector', '')
        
        if js_render:
            if PLAYWRIGHT_AVAILABLE:
                return self._scrape_with_playwright(url, wait_selector)
            else:
                logger.warning(f"配置了 js_render=True，但未安装 Playwright。回退到普通 HTTP 请求: {url}")
                # 回退到普通的 HTML 爬取
                
        return self._scrape_from_html(url)
    
    def _scrape_with_playwright(self, url: str, wait_selector: str) -> List[Dict[str, str]]:
        """使用 Playwright 无头浏览器渲染并抓取"""
        try:
            logger.info(f"正在使用 Playwright 渲染友链页面: {url}")
            with sync_playwright() as p:
                browser = p.chromium.launch(headless=True)
                # Playwright 默认超时单位为毫秒
                context = browser.new_context(user_agent=self.user_agent)
                page = context.new_page()
                # 浏览器渲染通常比普通请求慢，给予更多宽容时间（默认 30s 或常规超时的 3 倍）
                render_timeout = max(30, self.request_timeout * 3)
                page.set_default_timeout(render_timeout * 1000)
                
                logger.debug(f"正在访问页面并等待加载: {url}")
                page.goto(url, wait_until='load', timeout=render_timeout * 1000)
                
                if wait_selector:
                    logger.debug(f"等待选择器加载: {wait_selector}")
                    page.wait_for_selector(wait_selector, state='attached')
                else:
                    # 额外等待确保动态内容加载
                    page.wait_for_timeout(3000)
                
                html_content = page.content()
                browser.close()
                
            return self._parse_html(html_content, url)
        except Exception as e:
            logger.error(f"Playwright 渲染页面失败 {url}: {e}")
            return []
            
    def _scrape_from_html(self, url: str) -> List[Dict[str, str]]:
        """从友链 HTML 页面爬取链接（使用 requests）"""
        try:
            logger.info(f"正在通过 HTTP GET 爬取友链页面: {url}")
            response = self.session.get(url, timeout=self.request_timeout)
            response.encoding = 'utf-8'
            response.raise_for_status()
            return self._parse_html(response.text, url)
        except requests.Timeout:
            logger.error(f"爬取友链页面超时 {url}")
            return []
        except requests.HTTPError as e:
            logger.error(f"爬取友链页面HTTP错误 {url}: {e.response.status_code}")
            return []
        except Exception as e:
            logger.error(f"爬取友链页面失败 {url}: {e}")
            return []
            
    def _parse_html(self, html_content: str, base_url: str) -> List[Dict[str, str]]:
        """公用的 HTML 解析逻辑"""
        try:
            soup = BeautifulSoup(html_content, 'html.parser')
            links = []
            author_elements = soup.select(self.rules.get('author', [{}])[0].get('selector', ''))
            
            for author_elem in author_elements:
                try:
                    # 查找该作者元素对应的链接
                    link_elem = author_elem.find_parent().find('a') if author_elem.find_parent() else author_elem
                    if not link_elem:
                        link_elem = author_elem
                    
                    link_url = link_elem.get('href') or link_elem.get('data-href', '')
                    author_name = author_elem.get_text(strip=True) or link_elem.get_text(strip=True)
                    
                    # 尝试获取头像
                    avatar = ''
                    img_elem = author_elem.find_parent().find('img') if author_elem.find_parent() else None
                    if not img_elem:
                        img_elem = author_elem.find('img')
                    if img_elem:
                        avatar = img_elem.get('src', '')
                    
                    if link_url:
                        # 规范化URL
                        if not link_url.startswith('http'):
                            link_url = urljoin(base_url, link_url)
                        
                        # 处理重定向链接 (如 xiaoten.com/pages/redirect/#target=...)
                        link_url = self._unwrap_redirect_url(link_url)
                    
                    if link_url and author_name:
                        links.append({
                            'name': author_name,
                            'url': link_url,
                            'avatar': avatar
                        })
                except Exception as e:
                    logger.debug(f"解析单条链接失败: {e}")
                    continue
            
            logger.info(f"从{base_url}成功解析出{len(links)}条链接")
            return links
        except Exception as e:
            logger.error(f"解析 HTML 内容失败 {base_url}: {e}")
            return []
            
    def _unwrap_redirect_url(self, url: str) -> str:
        """解析并提取重定向链接中的真实目标 URL
        
        支持处理 #target=... 或 ?target=... 格式的重定向
        """
        try:
            parsed = urlparse(url)
            # 优先从 fragment (#) 中尝试提取 (适用于小十博客的跳转页)
            if parsed.fragment:
                # 兼容 target=... 这种格式
                params = parse_qs(parsed.fragment.lstrip('#'))
                target = params.get('target', [None])[0]
                if target:
                    return unquote(target)
            
            # 再从 query (?) 中尝试提取
            if parsed.query:
                params = parse_qs(parsed.query)
                target = params.get('target', [None])[0]
                if target:
                    return unquote(target)
            
            return url
        except Exception as e:
            logger.debug(f"解析重定向链接失败 {url}: {e}")
            return url


class RSSFetcher:
    """RSS源获取器"""
    
    def __init__(self, feed_suffixes: List[str], max_posts: int, cache_manager: Optional['CacheManager'] = None, 
                 request_timeout: int = 10, feed_check_timeout: int = 5, 
                 request_retries: int = 1, retry_backoff: float = 0.3, user_agent: str = None):
        self.feed_suffixes = feed_suffixes
        self.max_posts = max_posts
        self.cache = cache_manager
        self.request_timeout = request_timeout
        self.feed_check_timeout = feed_check_timeout
        self.request_retries = request_retries
        self.retry_backoff = retry_backoff
        self.user_agent = user_agent or DEFAULT_CONFIG['USER_AGENT']
        self.session = self._create_session()
        self.check_session = self._create_check_session()
        # 最近一次获取/解析 RSS 时的错误信息（字符串），供外部查询
        self.last_error: Optional[str] = None
    
    def _create_session(self) -> requests.Session:
        """创建带重试机制的requests会话（用于获取RSS内容）"""
        session = requests.Session()
        
        retry_strategy = Retry(
            total=self.request_retries,
            backoff_factor=self.retry_backoff,
            status_forcelist=[429, 500, 502, 503, 504],
            allowed_methods=["GET", "HEAD"]
        )
        
        adapter = HTTPAdapter(max_retries=retry_strategy)
        session.mount("http://", adapter)
        session.mount("https://", adapter)
        
        session.headers.update({'User-Agent': self.user_agent})
        session.verify = False
        return session
    
    def _create_check_session(self) -> requests.Session:
        """创建不进行重试的会话（用于快速检查Feed URL）"""
        session = requests.Session()
        
        # 不进行任何重试，快速失败
        adapter = HTTPAdapter(max_retries=0)
        session.mount("http://", adapter)
        session.mount("https://", adapter)
        
        session.headers.update({'User-Agent': self.user_agent})
        session.verify = False
        return session
    
    def find_feed_url(self, base_url: str, custom_suffix: Optional[str] = None) -> Optional[str]:
        """寻找站点的RSS源URL
        
        优先级：
        1. 检查缓存
        2. 尝试自定义后缀（如果有）
        3. 尝试常见Feed后缀（快速失败）
        """
        # 先检查缓存
        if self.cache:
            cached_url = self.cache.get_cached_feed_url(base_url)
            if cached_url:
                if self._check_feed_url(cached_url):
                    logger.debug(f"✓ 使用缓存的Feed: {cached_url}")
                    return cached_url
        
        # 确保base_url以/结尾
        base_url_normalized = base_url if base_url.endswith('/') else base_url + '/'
        
        # 如果指定了自定义后缀，首先尝试
        if custom_suffix:
            feed_url = urljoin(base_url_normalized, custom_suffix)
            if self._check_feed_url(feed_url):
                if self.cache:
                    self.cache.set_feed_url(base_url.rstrip('/'), feed_url)
                return feed_url
        
        # 尝试常见的Feed后缀
        for suffix in self.feed_suffixes:
            feed_url = urljoin(base_url_normalized, suffix)
            if self._check_feed_url(feed_url):
                if self.cache:
                    self.cache.set_feed_url(base_url.rstrip('/'), feed_url)
                return feed_url
        
        return None
    
    def _check_feed_url(self, url: str) -> bool:
        """检查URL是否是有效的Feed源（快速检查，不重试）"""
        try:
            # 使用不重试的会话和更短的超时
            response = self.check_session.get(url, timeout=self.feed_check_timeout)
            
            if response.status_code != 200:
                self.last_error = f"HTTP {response.status_code}"
                logger.debug(f"Feed URL检查失败 {url} (HTTP {response.status_code})")
                return False
            
            content_type = response.headers.get('content-type', '').lower()
            text_lower = response.text[:500].lower()  # 只检查前500字符
            
            # 检查是否是有效的XML/RSS/Atom源
            is_feed = ('xml' in content_type or 'rss' in content_type or 'feed' in content_type or
                      '<?xml' in text_lower or '<rss' in text_lower or '<feed' in text_lower)
            
            if is_feed:
                logger.debug(f"✓ 找到有效Feed源: {url}")
            else:
                self.last_error = "not_feed_format"
                logger.debug(f"✗ URL不是Feed格式: {url}")

            return is_feed
                
        except requests.Timeout:
            logger.debug(f"Feed URL检查超时: {url}")
            return False
        except requests.ConnectionError:
            logger.debug(f"Feed URL连接失败: {url}")
            return False
        except Exception as e:
            logger.debug(f"Feed URL检查异常 {url}: {type(e).__name__}")
            return False
    
    def fetch_feed(self, feed_url: str) -> Optional[feedparser.FeedParserDict]:
        """获取和解析RSS源"""
        try:
            logger.info(f"正在获取RSS源: {feed_url}")
            
            # 使用requests获取内容，然后传给feedparser
            response = self.session.get(feed_url, timeout=self.request_timeout)
            
            if response.status_code != 200:
                self.last_error = f"HTTP {response.status_code}"
                logger.warning(f"获取RSS源失败，HTTP {response.status_code}: {feed_url}")
                return None
            
            feed = feedparser.parse(response.content)
            
            if feed.bozo and isinstance(feed.bozo_exception, Exception):
                self.last_error = str(feed.bozo_exception)
                logger.debug(f"RSS解析异常 {feed_url}: {feed.bozo_exception}")
            
            if not feed.entries:
                # 无条目视为解析/内容问题
                self.last_error = "empty_or_unparseable"
                logger.warning(f"RSS源为空或无法解析: {feed_url}")
                return None
            
            return feed
        except requests.Timeout:
            self.last_error = 'timeout'
            logger.warning(f"获取RSS源超时: {feed_url}")
            return None
        except requests.ConnectionError as e:
            self.last_error = type(e).__name__
            logger.warning(f"获取RSS源连接错误 {feed_url}: {type(e).__name__}")
            return None
        except requests.HTTPError as e:
            self.last_error = f"HTTPError {e.response.status_code}"
            logger.warning(f"获取RSS源HTTP错误 {feed_url}: {e.response.status_code}")
            return None
        except Exception as e:
            self.last_error = str(e)
            logger.warning(f"获取RSS源失败 {feed_url}: {type(e).__name__}")
            return None


class DataAggregator:
    """数据聚合器"""
    
    def __init__(self, max_posts: int, outdate_days: int, timezone_correction: bool = True, sort_by: str = 'pub_date'):
        self.max_posts = max_posts
        self.outdate_days = outdate_days
        self.timezone_correction = timezone_correction
        self.sort_by = sort_by  # 'pub_date' 或 'updated_at'
        # 如果 outdate_days <= 0 则表示不限制过期，cutoff_time 设为 None
        if outdate_days and outdate_days > 0:
            self.cutoff_time = get_beijing_time() - timedelta(days=outdate_days)
        else:
            self.cutoff_time = None
    
    def aggregate_feed(self, site_info: Dict[str, str], feed: feedparser.FeedParserDict) -> Dict[str, Any]:
        """聚合单个站点的Feed数据"""
        site_data = {
            'name': site_info['name'],
            'url': site_info['url'],
            'avatar': site_info['avatar'],
            'feed_url': site_info.get('feed_url', ''),
            'posts': []
        }
        
        # 提取Feed信息
        feed_title = feed.feed.get('title', site_info['name'])
        
        posts = []
        for entry in feed.entries:
            try:
                # 获取原始时间字符串
                published_str = getattr(entry, 'published', '')
                updated_str = getattr(entry, 'updated', '')

                # 处理发布时间
                if hasattr(entry, 'published_parsed') and entry.published_parsed:
                    pub_time = parse_feed_time(entry.published_parsed, self.timezone_correction, published_str or None)
                elif hasattr(entry, 'updated_parsed') and entry.updated_parsed:
                    pub_time = parse_feed_time(entry.updated_parsed, self.timezone_correction, updated_str or None)
                else:
                    # 没有解析到任何时间，使用当前北京时间
                    pub_time = get_beijing_time()
                
                # 过滤过期文章（当设置为0或负数时表示不限制）
                if self.cutoff_time is not None and pub_time < self.cutoff_time:
                    continue
                
                # 处理更新时间
                if hasattr(entry, 'updated_parsed') and entry.updated_parsed:
                    update_time = parse_feed_time(entry.updated_parsed, self.timezone_correction, updated_str or None)
                else:
                    update_time = pub_time
                
                post = {
                    'title': entry.get('title', '无标题'),
                    'link': entry.get('link', ''),
                    'description': entry.get('summary', ''),
                    'pub_date': pub_time.isoformat(),
                    'updated_at': update_time.isoformat(),
                    'author': entry.get('author', '')
                }
                posts.append(post)
            except Exception as e:
                logger.debug(f"处理Feed条目失败: {e}")
                continue
        
        # 按配置的方式排序并限制数量
        posts.sort(key=lambda x: x[self.sort_by], reverse=True)
        site_data['posts'] = posts[:self.max_posts] if self.max_posts > 0 else posts
        
        return site_data
    
    def merge_data(self, all_sites: List[Dict[str, Any]]) -> Dict[str, Any]:
        """合并所有站点数据"""
        all_posts = []
        
        # 收集所有文章
        for site in all_sites:
            for post in site['posts']:
                post['site_name'] = site['name']
                post['site_url'] = site['url']
                post['avatar'] = site['avatar']
                all_posts.append(post)
        
        # 按配置的方式排序
        all_posts.sort(key=lambda x: x[self.sort_by], reverse=True)
        
        return {
            'updated_at': get_beijing_time().isoformat(),
            'total_sites': len(all_sites),
            'total_posts': len(all_posts),
            'sites': all_sites,
            'all_posts': all_posts
        }


class FriendRSSAggregator:
    """主控制器"""
    
    def __init__(self, config_path: str = 'setting.yaml'):
        self.config = ConfigParser(config_path)
        self.output_name = self.config.get_output_filename()
        self.previous_data = self._load_previous_output(self.output_name)
        self.cache = CacheManager(self.config.get_cache_file())
        self.site_filter = SiteFilter(
            self.config.get_block_sites(),
            self.config.get_block_site_reverse()
        )
        self.scraper = LinkPageScraper(
            self.config.get_link_page_rules(),
            self.config.get_request_timeout(),
            self.config.get_user_agent()
        )
        self.fetcher = RSSFetcher(
            self.config.get_feed_suffixes(),
            self.config.get_max_posts(),
            self.cache,
            self.config.get_request_timeout(),
            self.config.get_feed_check_timeout(),
            self.config.get_request_retries(),
            self.config.get_retry_backoff(),
            self.config.get_user_agent()
        )
        self.aggregator = DataAggregator(
            self.config.get_max_posts(),
            self.config.get_outdate_days(),
            self.config.get_timezone_correction(),
            self.config.get_sort_by()
        )
        # 用于记录获取 RSS 失败的站点列表
        self.failed_sites: List[Dict[str, Any]] = []

    def _load_previous_output(self, output_path: str) -> Optional[dict]:
        """读取上一版输出，作为网络波动时的兜底基准。"""
        if not output_path or not os.path.exists(output_path):
            return None

        try:
            with open(output_path, 'r', encoding='utf-8') as f:
                data = json.load(f)
            if isinstance(data, dict) and isinstance(data.get('sites'), list):
                logger.info(f"已加载上一版输出用于兜底: {output_path}")
                return data
            logger.warning(f"上一版输出格式无效，跳过兜底: {output_path}")
        except Exception as e:
            logger.warning(f"读取上一版输出失败，跳过兜底: {e}")
        return None

    def _previous_site_index(self) -> Dict[str, Dict[str, Any]]:
        """按站点 URL 建立上一版站点索引。"""
        if not self.previous_data:
            return {}

        index = {}
        for site in self.previous_data.get('sites', []):
            key = normalize_site_url(site.get('url', ''))
            if key:
                index[key] = site
        return index

    def _clone_stale_site(self, site: Dict[str, Any], reason: str, last_error: str) -> Dict[str, Any]:
        """复制上一版站点数据，并标记为旧数据兜底。"""
        cloned = json.loads(json.dumps(site, ensure_ascii=False))
        cloned['stale'] = True
        cloned['stale_reason'] = reason
        cloned['last_error'] = last_error
        cloned['last_success_at'] = (
            site.get('last_success_at') or self.previous_data.get('updated_at')
            if self.previous_data else None
        )
        return cloned

    def _apply_stale_fallback(self, all_sites: List[Dict[str, Any]], all_links: List[Dict[str, str]]) -> List[Dict[str, Any]]:
        """用上一版成功数据补回本轮失败或缺失的站点。"""
        if not self.config.get_stale_fallback_enabled() or not self.previous_data:
            return all_sites

        previous_sites = self._previous_site_index()
        if not previous_sites:
            return all_sites

        current_keys = {normalize_site_url(site.get('url', '')) for site in all_sites}
        link_keys = {normalize_site_url(link.get('url', '')) for link in all_links}
        failed_by_key = {
            normalize_site_url(item.get('url', '')): item
            for item in self.failed_sites
            if normalize_site_url(item.get('url', ''))
        }

        restored = 0
        for key, failure in failed_by_key.items():
            if key in current_keys or key not in previous_sites:
                continue
            reason = failure.get('reason') or 'fetch_failed'
            all_sites.append(self._clone_stale_site(previous_sites[key], 'fetch_failed', reason))
            current_keys.add(key)
            restored += 1

        previous_count = len(previous_sites)
        link_count_is_suspicious = (
            previous_count > 0 and
            len(link_keys) < previous_count * self.config.get_min_site_retention_ratio()
        )

        if self.config.get_stale_fallback_include_missing_sites() and link_count_is_suspicious:
            missing_restored = 0
            for key, previous_site in previous_sites.items():
                if key in current_keys or key in link_keys:
                    continue
                all_sites.append(self._clone_stale_site(previous_site, 'not_seen_this_run', 'link_page_missing'))
                current_keys.add(key)
                missing_restored += 1
            restored += missing_restored
        elif self.config.get_stale_fallback_include_missing_sites():
            logger.debug("本轮友链数量未明显缩水，跳过缺失站点兜底")

        if restored:
            logger.warning(f"已用上一版数据兜底恢复 {restored} 个站点")
        return all_sites

    def validate_publish_quality(self, data: dict):
        """对输出结果做发布门禁，防止低质量结果覆盖线上数据。"""
        previous = self.previous_data
        if not previous:
            logger.info("没有上一版输出，跳过相对质量门禁")
            return

        previous_sites = int(previous.get('total_sites') or len(previous.get('sites', [])) or 0)
        previous_posts = int(previous.get('total_posts') or len(previous.get('all_posts', [])) or 0)
        current_sites = int(data.get('total_sites') or 0)
        current_posts = int(data.get('total_posts') or 0)
        failed_count = len(data.get('failed_sites') or [])

        failures = []
        min_site_ratio = self.config.get_min_site_retention_ratio()
        min_post_ratio = self.config.get_min_post_retention_ratio()
        max_failed = self.config.get_max_failed_sites_for_publish()

        if previous_sites > 0 and current_sites < previous_sites * min_site_ratio:
            failures.append(f"站点数缩水过多: {current_sites}/{previous_sites}，阈值 {min_site_ratio:.0%}")
        if previous_posts > 0 and current_posts < previous_posts * min_post_ratio:
            failures.append(f"文章数缩水过多: {current_posts}/{previous_posts}，阈值 {min_post_ratio:.0%}")
        if max_failed >= 0 and failed_count > max_failed:
            failures.append(f"失败站点过多: {failed_count}，上限 {max_failed}")

        if failures:
            message = "本次 RSS 输出未通过发布门禁，已停止覆盖旧数据: " + "；".join(failures)
            logger.error(message)
            raise RuntimeError(message)

        logger.info("RSS 输出通过发布门禁")
    
    def get_all_links(self) -> List[Dict[str, str]]:
        """获取所有友链
        
        处理顺序：
        1. 从友链页面爬取链接
        2. 对爬取的链接进行屏蔽检查
        3. 尝试获取RSS源并缓存
        4. 添加手动配置的链接
        """
        all_links = []
        url_set = set()
        
        # 【第一步】从友链页面爬取链接，并尝试发现RSS源
        logger.info("【第一步】爬取友链页面并发现RSS源...")
        for page_url in self.config.get_link_pages():
            scraped_links = self.scraper.scrape(page_url)
            for link in scraped_links:
                # 检查是否被屏蔽
                if self.site_filter.is_blocked(link['url']):
                    logger.debug(f"爬取友链被屏蔽: {link['name']} ({link['url']})")
                    continue
                
                # 去重
                if link['url'] in url_set:
                    logger.debug(f"友链已存在，跳过重复: {link['name']}")
                    continue
                
                # 尝试发现RSS源
                feed_url = self.fetcher.find_feed_url(link['url'])
                if feed_url:
                    link['feed_url'] = feed_url
                    logger.debug(f"已发现RSS源: {link['name']} -> {feed_url}")
                else:
                    logger.debug(f"未找到RSS源: {link['name']}")
                
                all_links.append(link)
                url_set.add(link['url'])
                logger.debug(f"添加爬取友链: {link['name']} ({link['url']})")
        
        # 【第二步】添加手动配置的链接
        logger.info("【第二步】添加手动配置的友链...")
        manual_links = self.config.get_manual_links()
        for link in manual_links:
            # 手动配置的友链不受黑名单限制，但需要检查去重（忽略URL末尾斜杠差异）
            norm_url = link['url'].rstrip('/')
            existing_link = next((l for l in all_links if l.get('url', '').rstrip('/') == norm_url), None)

            if existing_link:
                # 已存在该站点：如果手动配置提供了自定义feed_suffix，则覆盖已有配置
                if link.get('feed_suffix'):
                    base = (existing_link['url'] if existing_link['url'].endswith('/') else existing_link['url'] + '/')
                    try:
                        feed_url = urljoin(base, link['feed_suffix'])
                        existing_link['feed_url'] = feed_url
                        existing_link['name'] = link['name'] or existing_link.get('name', '')
                        if link.get('avatar'):
                            existing_link['avatar'] = link['avatar']
                        logger.debug(f"手动友链覆盖已存在项: {link['name']} -> {feed_url}")
                    except Exception:
                        logger.debug(f"构建自定义RSS源失败: {link['name']} ({existing_link.get('url')})")
                else:
                    logger.debug(f"手动友链已存在，跳过重复: {link['name']}")
                continue
            
            # 如果有自定义Feed后缀，按用户选择 A：跳过快速检查，直接拼接并设置为 feed_url（fetch 阶段仍会尝试解析）
            if link.get('feed_suffix'):
                try:
                    base = link['url'] if link['url'].endswith('/') else link['url'] + '/'
                    feed_url = urljoin(base, link['feed_suffix'])
                    link['feed_url'] = feed_url
                    logger.debug(f"已设置自定义RSS源（跳过检查）: {link['name']} -> {feed_url}")
                except Exception:
                    logger.debug(f"构建自定义RSS源失败: {link['name']} ({link.get('url')})")
            else:
                feed_url = self.fetcher.find_feed_url(link['url'])
                if feed_url:
                    link['feed_url'] = feed_url
                    logger.debug(f"已发现RSS源: {link['name']} -> {feed_url}")
            
            all_links.append(link)
            url_set.add(link['url'])
            logger.debug(f"添加手动友链: {link['name']} ({link['url']})")
        
        logger.info(f"共获取{len(all_links)}条有效友链")
        return all_links
    
    def process_site(self, link: Dict[str, str]) -> Optional[Dict[str, Any]]:
        """处理单个站点，获取其RSS数据"""
        try:
            # 如果之前已经发现了Feed URL，直接使用
            feed_url = link.get('feed_url')
            
            if not feed_url:
                # 如果没有预先发现，再次尝试寻找（备用）
                feed_url = self.fetcher.find_feed_url(
                    link['url'],
                    link.get('feed_suffix')
                )
            
            if not feed_url:
                logger.warning(f"无法找到{link['name']}的RSS源: {link['url']}")
                # 记录失败站点
                self.failed_sites.append({
                    'name': link.get('name'),
                    'url': link.get('url'),
                    'feed_url': None,
                    'reason': 'no_feed_found'
                })
                return None
            
            # 获取Feed
            feed = self.fetcher.fetch_feed(feed_url)
            if not feed:
                # 记录 fetch 失败及其原因（fetcher.last_error）
                self.failed_sites.append({
                    'name': link.get('name'),
                    'url': link.get('url'),
                    'feed_url': feed_url,
                    'reason': getattr(self.fetcher, 'last_error', 'fetch_failed')
                })
                return None
            
            site_info = {
                'name': link['name'],
                'url': link['url'],
                'avatar': link.get('avatar', ''),
                'feed_url': feed_url
            }
            
            site_data = self.aggregator.aggregate_feed(site_info, feed)
            logger.info(f"成功处理{link['name']}: 获取{len(site_data['posts'])}篇文章")
            return site_data
        
        except Exception as e:
            logger.error(f"处理站点{link.get('name', link['url'])}失败: {e}")
            self.failed_sites.append({
                'name': link.get('name'),
                'url': link.get('url'),
                'feed_url': link.get('feed_url'),
                'reason': str(e)
            })
            return None
    
    def run(self) -> dict:
        """执行主流程"""
        logger.info("=" * 50)
        logger.info("开始友链RSS聚合")
        logger.info("=" * 50)
        
        # 获取所有链接
        all_links = self.get_all_links()
        
        # 处理每个站点
        max_workers = self.config.get_max_workers()
        
        if max_workers and max_workers > 0:
            # 并发处理
            logger.info(f"使用{max_workers}个线程并发处理友链...")
            all_sites = []
            with ThreadPoolExecutor(max_workers=max_workers) as executor:
                # 提交所有任务
                future_to_link = {executor.submit(self.process_site, link): link for link in all_links}
                
                # 获取结果
                for future in as_completed(future_to_link):
                    try:
                        site_data = future.result()
                        if site_data:
                            all_sites.append(site_data)
                    except Exception as e:
                        link = future_to_link[future]
                        logger.error(f"并发处理站点{link.get('name')}时发生异常: {e}")
        else:
            # 串行处理
            all_sites = []
            for link in all_links:
                site_data = self.process_site(link)
                if site_data:
                    all_sites.append(site_data)

        # 网络波动导致本轮抓取失败时，优先保留上一版成功数据，避免线上友圈突然缩水。
        all_sites = self._apply_stale_fallback(all_sites, all_links)
        
        # 合并数据
        final_data = self.aggregator.merge_data(all_sites)
        # 把失败站点信息放入最终结果
        final_data['failed_sites'] = self.failed_sites
        
        logger.info("=" * 50)
        logger.info(f"聚合完成: {final_data['total_sites']}个站点, {final_data['total_posts']}篇文章")
        logger.info("=" * 50)
        
        # 保存缓存
        self.cache.save()
        
        return final_data
    
    def save_to_file(self, data: dict, output_path: str = 'data.json'):
        """保存数据到JSON文件"""
        try:
            with open(output_path, 'w', encoding='utf-8') as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
            logger.info(f"数据已保存到{output_path}")
        except Exception as e:
            logger.error(f"保存文件失败: {e}")


def main():
    """主函数"""
    try:
        aggregator = FriendRSSAggregator('setting.yaml')
        data = aggregator.run()
        aggregator.validate_publish_quality(data)
        output_name = aggregator.output_name
        aggregator.save_to_file(data, output_name)
        
        # 输出统计信息
        logger.info("📊 最终统计:")
        logger.info(f"  ✓ 总站点数: {data['total_sites']}")
        logger.info(f"  ✓ 总文章数: {data['total_posts']}")
        logger.info(f"  ✓ 更新时间: {data['updated_at']}")
        logger.info("✅ 程序执行成功!")
    except Exception as e:
        logger.error(f"❌ 程序执行失败: {e}", exc_info=True)
        raise


if __name__ == '__main__':
    main()
