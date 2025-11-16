#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
友链RSS订阅聚合程序
从友链页面和手动配置列表中获取RSS源，聚合成data.json
"""

import os
import json
import re
import logging
from datetime import datetime, timedelta, timezone
from typing import List, Dict, Any, Tuple, Optional
from urllib.parse import urljoin, urlparse
import hashlib
from time import sleep

import requests
import yaml
from bs4 import BeautifulSoup
import feedparser
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
import urllib3

# 禁用SSL警告
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

# 配置常量
REQUEST_TIMEOUT = 10
REQUEST_RETRIES = 1  # 减少重试次数，避免过多尝试
RETRY_BACKOFF = 0.3
FEED_CHECK_TIMEOUT = 5  # Feed URL检查使用更短的超时
USER_AGENT = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
CACHE_FILE = 'feed_cache.json'

# 定义北京时间时区 (UTC+8)
BEIJING_TZ = timezone(timedelta(hours=8))

def get_beijing_time():
    """获取当前北京时间"""
    return datetime.now(BEIJING_TZ)

def parse_feed_time(time_tuple, timezone_correction=True):
    """解析feed时间
    
    Args:
        time_tuple: feedparser解析的时间元组
        timezone_correction: 是否进行时区校正（转换为北京时间）
    """
    if not time_tuple:
        return get_beijing_time()
    
    try:
        if timezone_correction:
            # 开启时区校正：将时间转换为北京时间
            # 将时间元组转换为UTC时间
            utc_dt = datetime(*time_tuple[:6], tzinfo=timezone.utc)
            # 转换为北京时间
            return utc_dt.astimezone(BEIJING_TZ)
        else:
            # 关闭时区校正：直接使用RSS源中的时间
            # 直接构造北京时间对象，不进行时区转换
            return datetime(*time_tuple[:6], tzinfo=BEIJING_TZ)
    except Exception as e:
        logger.warning(f"时间解析失败: {e}, 使用当前时间代替")
        return get_beijing_time()


class CacheManager:
    """缓存管理器，存储已发现的RSS源和文章ID"""
    
    def __init__(self, cache_file: str = CACHE_FILE):
        self.cache_file = cache_file
        self.cache = self._load_cache()
    
    def _load_cache(self) -> dict:
        """加载缓存"""
        if os.path.exists(self.cache_file):
            try:
                with open(self.cache_file, 'r', encoding='utf-8') as f:
                    return json.load(f)
            except Exception as e:
                logger.warning(f"加载缓存失败: {e}")
                return self._init_cache()
        return self._init_cache()
    
    def _init_cache(self) -> dict:
        """初始化缓存结构"""
        return {
            'feed_urls': {},  # {site_url: feed_url}
            'article_ids': set(),  # 已处理的文章ID（用于去重）
            'last_update': None
        }
    
    def save(self):
        """保存缓存"""
        try:
            # 将set转换为list以便JSON序列化
            cache_to_save = self.cache.copy()
            cache_to_save['article_ids'] = list(self.cache.get('article_ids', []))
            
            with open(self.cache_file, 'w', encoding='utf-8') as f:
                json.dump(cache_to_save, f, ensure_ascii=False, indent=2)
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
    
    def get_article_id(self, article: dict) -> str:
        """生成文章唯一ID"""
        # 使用标题和发布日期的组合作为ID
        key = f"{article.get('title', '')}{article.get('pub_date', '')}".encode('utf-8')
        return hashlib.md5(key).hexdigest()
    
    def is_article_seen(self, article: dict) -> bool:
        """检查文章是否已处理过"""
        if not isinstance(self.cache.get('article_ids'), set):
            self.cache['article_ids'] = set()
        article_id = self.get_article_id(article)
        return article_id in self.cache['article_ids']
    
    def mark_article_seen(self, article: dict):
        """标记文章为已处理"""
        if not isinstance(self.cache.get('article_ids'), set):
            self.cache['article_ids'] = set()
        article_id = self.get_article_id(article)
        self.cache['article_ids'].add(article_id)


class ConfigParser:
    """解析setting.yaml配置文件"""
    
    def __init__(self, config_path: str = 'setting.yaml'):
        self.config_path = config_path
        self.config = self._load_config()
    
    def _load_config(self) -> dict:
        """加载YAML配置文件"""
        with open(self.config_path, 'r', encoding='utf-8') as f:
            return yaml.safe_load(f)
    
    def get_link_pages(self) -> List[str]:
        """获取需要爬取的友链页面URL列表"""
        links = []
        for item in self.config.get('LINK', []):
            if isinstance(item, dict) and 'link' in item:
                links.append(item['link'])
        return links
    
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
        """获取过期文章天数"""
        return self.config.get('OUTDATE_CLEAN', 180)
    
    def get_timezone_correction(self) -> bool:
        """获取是否开启时区校正"""
        return self.config.get('TIMEZONE_CORRECTION', True)


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
    
    def __init__(self, rules: dict):
        self.rules = rules
        self.session = self._create_session()
    
    def _create_session(self) -> requests.Session:
        """创建带重试机制的requests会话"""
        session = requests.Session()
        
        # 配置重试策略：只重试1次，快速失败
        retry_strategy = Retry(
            total=REQUEST_RETRIES,
            backoff_factor=RETRY_BACKOFF,
            status_forcelist=[429, 500, 502, 503, 504],
            allowed_methods=["GET", "HEAD"],
            raise_on_status=False  # 不要在状态错误时抛出异常
        )
        
        adapter = HTTPAdapter(max_retries=retry_strategy)
        session.mount("http://", adapter)
        session.mount("https://", adapter)
        
        session.headers.update({'User-Agent': USER_AGENT})
        session.verify = False  # 禁用SSL验证，避免自签名证书错误
        return session
    
    def scrape(self, url: str) -> List[Dict[str, str]]:
        """从友链页面爬取链接"""
        try:
            logger.info(f"正在爬取友链页面: {url}")
            response = self.session.get(url, timeout=REQUEST_TIMEOUT)
            response.encoding = 'utf-8'
            response.raise_for_status()
            
            soup = BeautifulSoup(response.text, 'html.parser')
            
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
                    
                    if link_url and author_name:
                        # 规范化URL
                        if not link_url.startswith('http'):
                            link_url = urljoin(url, link_url)
                        
                        links.append({
                            'name': author_name,
                            'url': link_url,
                            'avatar': avatar
                        })
                except Exception as e:
                    logger.debug(f"爬取单条链接失败: {e}")
                    continue
            
            logger.info(f"从{url}成功爬取{len(links)}条链接")
            return links
        except requests.Timeout:
            logger.error(f"爬取友链页面超时 {url}")
            return []
        except requests.HTTPError as e:
            logger.error(f"爬取友链页面HTTP错误 {url}: {e.response.status_code}")
            return []
        except Exception as e:
            logger.error(f"爬取友链页面失败 {url}: {e}")
            return []


class RSSFetcher:
    """RSS源获取器"""
    
    def __init__(self, feed_suffixes: List[str], max_posts: int, cache_manager: Optional['CacheManager'] = None):
        self.feed_suffixes = feed_suffixes
        self.max_posts = max_posts
        self.session = self._create_session()
        self.check_session = self._create_check_session()  # 用于快速检查Feed URL的会话
        self.cache = cache_manager
        # 最近一次获取/解析 RSS 时的错误信息（字符串），供外部查询
        self.last_error: Optional[str] = None
    
    def _create_session(self) -> requests.Session:
        """创建带重试机制的requests会话（用于获取RSS内容）"""
        session = requests.Session()
        
        retry_strategy = Retry(
            total=REQUEST_RETRIES,
            backoff_factor=RETRY_BACKOFF,
            status_forcelist=[429, 500, 502, 503, 504],
            allowed_methods=["GET", "HEAD"]
        )
        
        adapter = HTTPAdapter(max_retries=retry_strategy)
        session.mount("http://", adapter)
        session.mount("https://", adapter)
        
        session.headers.update({'User-Agent': USER_AGENT})
        session.verify = False
        return session
    
    def _create_check_session(self) -> requests.Session:
        """创建不进行重试的会话（用于快速检查Feed URL）"""
        session = requests.Session()
        
        # 不进行任何重试，快速失败
        adapter = HTTPAdapter(max_retries=0)
        session.mount("http://", adapter)
        session.mount("https://", adapter)
        
        session.headers.update({'User-Agent': USER_AGENT})
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
            response = self.check_session.get(url, timeout=FEED_CHECK_TIMEOUT)
            
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
            response = self.session.get(feed_url, timeout=REQUEST_TIMEOUT)
            
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
    
    def __init__(self, max_posts: int, outdate_days: int, timezone_correction: bool = True):
        self.max_posts = max_posts
        self.outdate_days = outdate_days
        self.timezone_correction = timezone_correction
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
                # 获取发布时间，根据时区校正设置进行处理
                pub_time = None
                if hasattr(entry, 'published_parsed') and entry.published_parsed:
                    pub_time = parse_feed_time(entry.published_parsed, self.timezone_correction)
                elif hasattr(entry, 'updated_parsed') and entry.updated_parsed:
                    pub_time = parse_feed_time(entry.updated_parsed, self.timezone_correction)
                else:
                    pub_time = get_beijing_time()
                
                # 过滤过期文章（当设置为0或负数时表示不限制）
                if self.cutoff_time is not None and pub_time < self.cutoff_time:
                    continue
                
                # 获取更新时间，根据时区校正设置进行处理
                update_time = None
                if hasattr(entry, 'updated_parsed') and entry.updated_parsed:
                    update_time = parse_feed_time(entry.updated_parsed, self.timezone_correction)
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
        
        # 按发布时间排序并限制数量
        posts.sort(key=lambda x: x['pub_date'], reverse=True)
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
        
        # 按时间排序
        all_posts.sort(key=lambda x: x['pub_date'], reverse=True)
        
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
        self.cache = CacheManager()
        self.site_filter = SiteFilter(
            self.config.get_block_sites(),
            self.config.get_block_site_reverse()
        )
        self.scraper = LinkPageScraper(self.config.get_link_page_rules())
        self.fetcher = RSSFetcher(
            self.config.get_feed_suffixes(),
            self.config.get_max_posts(),
            self.cache
        )
        self.aggregator = DataAggregator(
            self.config.get_max_posts(),
            self.config.get_outdate_days(),
            self.config.get_timezone_correction()  # 传递时区校正配置
        )
        # 用于记录获取 RSS 失败的站点列表
        self.failed_sites: List[Dict[str, Any]] = []
    
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
            # 检查是否被屏蔽
            if self.site_filter.is_blocked(link['url']):
                logger.debug(f"手动友链被屏蔽: {link['name']} ({link['url']})")
                continue
            
            # 去重
            if link['url'] in url_set:
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
        all_sites = []
        for link in all_links:
            site_data = self.process_site(link)
            if site_data:
                all_sites.append(site_data)
        
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
        aggregator.save_to_file(data, 'data.json')
        
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

