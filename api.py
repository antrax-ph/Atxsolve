import argparse
import asyncio
import json
import logging
import os
import re
import secrets
import shutil
import signal
import string
import sys
import threading
import time
import uuid
from datetime import datetime
from functools import wraps
from typing import Dict, List, Optional

from colorama import Fore, Style, init
from quart import Quart, jsonify, redirect, render_template, request, session
from rich.console import Console

import cf_clearance.solve as cf_clearance_solver
from core.browser import (
    BrowserConfig,
    close_browser,
    context_options,
    launch_browser,
)
from core.logger import get_logger
import turnstile.solve as turnstile_solver

init(autoreset=True)
logger = get_logger("SolverAPI")

ART_LINES = [
    " █████╗ ██╗  ██╗███████╗ ██████╗ ██╗    ██╗   ██╗███████╗██████╗ ",
    "██╔══██╗╚██╗██╔╝██╔════╝██╔═══██╗██║    ██║   ██║██╔════╝██╔══██╗",
    "███████║ ╚███╔╝ ███████╗██║   ██║██║    ██║   ██║█████╗  ██████╔╝",
    "██╔══██║ ██╔██╗ ╚════██║██║   ██║██║    ╚██╗ ██╔╝██╔══╝  ██╔══██╗",
    "██║  ██║██╔╝ ██╗███████║╚██████╔╝███████╗╚████╔╝ ███████╗██║  ██║",
    "╚═╝  ╚═╝╚═╝  ╚═╝╚══════╝ ╚═════╝ ╚══════╝ ╚═══╝  ╚══════╝╚═╝  ╚═╝",
]


def _build_gradient():
  waypoints = [
      (255, 220, 0),
      (255, 120, 0),
      (255, 0, 60),
      (200, 0, 255),
      (60, 0, 255),
      (0, 180, 255),
      (0, 255, 120),
      (255, 220, 0),
  ]
  steps = 40
  palette = []
  for i in range(len(waypoints) - 1):
    r0, g0, b0 = waypoints[i]
    r1, g1, b1 = waypoints[i + 1]
    for s in range(steps):
      t = s / steps
      r = int(r0 + (r1 - r0) * t)
      g = int(g0 + (g1 - g0) * t)
      b = int(b0 + (b1 - b0) * t)
      palette.append(f"\033[38;2;{r};{g};{b}m")
  return palette


GRADIENT = _build_gradient()
GRAD_LEN = len(GRADIENT)
BANNER_HEIGHT = len(ART_LINES) + 4
_log_area_start = BANNER_HEIGHT + 1
_rainbow_offset = 0
_terminal_lock = threading.Lock()
_rainbow_running = False
_rainbow_thread = None


def _move(row, col=1):
  return f"\033[{row};{col}H"


def _render_banner(offset):
  cols = shutil.get_terminal_size((120, 40)).columns
  out = ["\033[s", "\033[?25l"]
  out.append(_move(1))
  out.append("\033[2K")

  art_width = max(len(line) for line in ART_LINES)
  pad = max(0, (cols - art_width) // 2)
  padding = " " * pad

  CHAR_WIDTH = 9

  for i, line in enumerate(ART_LINES):
    out.append(_move(i + 2))
    out.append("\033[2K")
    rendered = padding
    j = 0
    while j < len(line):
      block = line[j : j + CHAR_WIDTH]
      color_idx = (j // CHAR_WIDTH + offset) % GRAD_LEN
      rendered += GRADIENT[color_idx] + block
      j += CHAR_WIDTH
    out.append(rendered + "\033[0m")

  info_row = len(ART_LINES) + 2
  info1 = "AXSolver Version 1.1"
  info2 = "Created by KrazyAxel"
  pad1 = max(0, (cols - len(info1)) // 2)
  pad2 = max(0, (cols - len(info2)) // 2)

  out.append(_move(info_row))
  out.append("\033[2K")
  out.append(f"{' ' * pad1}\033[38;5;214m{info1}\033[0m")
  out.append(_move(info_row + 1))
  out.append("\033[2K")
  out.append(f"{' ' * pad2}\033[38;5;214m{info2}\033[0m")
  out.append(_move(info_row + 2))
  out.append("\033[2K")
  out.append("\033[38;5;240m" + "─" * cols + "\033[0m")
  out.append("\033[u")
  out.append("\033[?25h")

  sys.__stdout__.write("".join(out))
  sys.__stdout__.flush()


def _rainbow_loop():
  global _rainbow_offset, _rainbow_running
  while _rainbow_running:
    with _terminal_lock:
      _render_banner(_rainbow_offset)
    _rainbow_offset = (_rainbow_offset + 1) % GRAD_LEN
    time.sleep(0.015)


def start_rainbow():
  global _rainbow_running, _rainbow_thread
  sys.__stdout__.write("\033[2J\033[H")
  sys.__stdout__.write("\n" * (_log_area_start + 1))
  sys.__stdout__.write(_move(_log_area_start))
  sys.__stdout__.flush()
  _rainbow_running = True
  _rainbow_thread = threading.Thread(target=_rainbow_loop, daemon=True)
  _rainbow_thread.start()


def stop_rainbow():
  global _rainbow_running
  _rainbow_running = False


class SplitTerminalHandler(logging.StreamHandler):

  def emit(self, record):
    try:
      msg = self.format(record)
      with _terminal_lock:
        sys.__stdout__.write(msg + "\n")
        sys.__stdout__.flush()
    except Exception:
      pass


def _install_split_handler():
  h = SplitTerminalHandler(sys.__stdout__)
  h.setFormatter(logging.Formatter("%(message)s"))
  root = logging.getLogger()
  root.handlers.clear()
  root.addHandler(h)
  for name, lgr in logging.Logger.manager.loggerDict.items():
    if isinstance(lgr, logging.Logger):
      lgr.handlers.clear()
      lgr.addHandler(h)
      lgr.propagate = False


CONTINUOUS_SESSIONS: dict = {}
CONTINUOUS_TOKEN_QUEUES: dict = {}
TOKENS_DIR = "tokens"
os.makedirs(TOKENS_DIR, exist_ok=True)
WIDGET_COUNT = 5
CLEANUP_INTERVAL_S = 600
TASK_TTL_S = 3600

ACTIVE_SESSIONS = {}
API_KEYS = {}

SERVER_START_TIME = time.time()
METRICS = {
    "solved": 0,
    "errors": 0,
    "in_flight": 0,
    "latencies": [],
    "recent_events": [],
}
METRICS_LOCK = asyncio.Lock()


def parse_proxy_spec(proxy_input) -> Optional[dict]:
  if not proxy_input:
    return None
  if isinstance(proxy_input, dict):
    if "server" in proxy_input:
      return proxy_input
    host = (
        proxy_input.get("host")
        or proxy_input.get("ip")
        or proxy_input.get("server")
    )
    port = proxy_input.get("port")
    username = proxy_input.get("username") or proxy_input.get("user")
    password = proxy_input.get("password") or proxy_input.get("pass")
    if not host or not port:
      return None
    res = {"server": f"http://{host}:{port}"}
    if username and password:
      res["username"] = str(username)
      res["password"] = str(password)
    return res

  if isinstance(proxy_input, str):
    proxy_str = proxy_input.strip()
    if not proxy_str:
      return None
    scheme = "http://"
    if "://" in proxy_str:
      scheme, proxy_str = proxy_str.split("://", 1)
      scheme = f"{scheme}://"

    if "@" in proxy_str:
      auth_part, host_part = proxy_str.split("@", 1)
      user, pwd = (
          auth_part.split(":", 1) if ":" in auth_part else (auth_part, "")
      )
      return {
          "server": f"{scheme}{host_part}",
          "username": user,
          "password": pwd,
      }

    parts = proxy_str.split(":")
    if len(parts) == 4:
      return {
          "server": f"{scheme}{parts[0]}:{parts[1]}",
          "username": parts[2],
          "password": parts[3],
      }
    elif len(parts) == 2:
      return {"server": f"{scheme}{parts[0]}:{parts[1]}"}
    else:
      return {"server": f"{scheme}{proxy_str}"}

  return None


def generate_api_key():
  random_part = "".join(
      secrets.choice(string.ascii_letters + string.digits) for _ in range(24)
  )
  return f"AXSolver-{random_part}"


def check_auth():
  return True


def check_api_key():
  return True


def login_required(f):

  @wraps(f)
  async def decorated_function(*args, **kwargs):
    return await f(*args, **kwargs)

  return decorated_function


async def solve_turnstile_widget(
    page,
    url: str,
    sitekey: str,
    action: Optional[str],
    cdata: Optional[str],
    widget_id: int,
    session_id: str = None,
) -> Optional[dict]:
  print(
      f"{Fore.YELLOW}🔍 Widget {widget_id} - Solving for:"
      f" {Fore.CYAN}{url}{Style.RESET_ALL}"
  )
  start_time = time.time()
  try:
    token, method = await turnstile_solver.solve(
        page, url, sitekey, action, cdata
    )
    elapsed = time.time() - start_time
    if not token:
      print(
          f"{Fore.RED}❌ Widget {widget_id} - Failed in"
          f" {elapsed:.2f}s{Style.RESET_ALL}"
      )
      return None

    site_name = re.sub(r"^https?://", "", url).split("/")[0].replace(".", "_")
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    main_file = os.path.join(TOKENS_DIR, f"solvedtokens-{site_name}.txt")
    with open(main_file, "a", encoding="utf-8") as f:
      f.write(f"{token}\n")

    log_file = os.path.join(TOKENS_DIR, "tokens_log.txt")
    with open(log_file, "a", encoding="utf-8") as f:
      f.write(f"[{timestamp}] ✅ Solved | {elapsed:.2f}s | {token}\n")

    if session_id and session_id in CONTINUOUS_TOKEN_QUEUES:
      CONTINUOUS_TOKEN_QUEUES[session_id].append({
          "token": token,
          "elapsed": elapsed,
          "widget_id": widget_id,
          "timestamp": datetime.now().isoformat(),
      })
      if session_id in CONTINUOUS_SESSIONS:
        CONTINUOUS_SESSIONS[session_id]["total_tokens"] = len(
            CONTINUOUS_TOKEN_QUEUES[session_id]
        )
      print(
          f"{Fore.GREEN}📥 Token added to queue: {session_id[:8]} (total:"
          f" {len(CONTINUOUS_TOKEN_QUEUES[session_id])}){Style.RESET_ALL}"
      )

    print(
        f"{Fore.GREEN}✅ Widget {widget_id} - Solved in"
        f" {elapsed:.2f}s{Style.RESET_ALL}"
    )
    print(f"{Fore.GREEN}🔑 Token: {Fore.CYAN}{token[:30]}...{Style.RESET_ALL}")

    return {
        "token": token,
        "method": method,
        "elapsed_time": elapsed,
        "widget_id": widget_id,
        "url": url,
        "sitekey": sitekey,
    }
  except Exception as e:
    err_str = str(e).split('\n')[0]
    print(f"{Fore.RED}❌ Widget {widget_id} - Error: {err_str}{Style.RESET_ALL}")
    return None


async def solve_continuous_widgets(
    url: str,
    sitekey: str,
    action: Optional[str],
    cdata: Optional[str],
    session_id: str,
    count: int = WIDGET_COUNT,
    headless: bool = True,
):
  print(
      f"{Fore.CYAN}🔄 Continuous session {session_id[:8]} started - {count}"
      f" widgets (sequential, no delay){Style.RESET_ALL}"
  )
  print(f"{Fore.CYAN}🔄 Headless mode: {headless}{Style.RESET_ALL}")

  CONTINUOUS_TOKEN_QUEUES[session_id] = []
  config = BrowserConfig(
      browser_type="chrome",
      headless=headless,
      useragent=None,
      proxy_support=False,
      debug=False,
  )

  batch_count = 0
  while CONTINUOUS_SESSIONS.get(session_id, {}).get("active", True):
    try:
      batch_count += 1
      start_time = time.time()
      print(f"{Fore.BLUE}📦 Batch {batch_count} starting...{Style.RESET_ALL}")

      driver = None
      browser = None
      context = None

      try:
        driver, browser = await launch_browser(config)
        context = await browser.new_context(
            **context_options(config, None)
        )
        for i in range(count):
          try:
            page = await context.new_page()
            await page.set_extra_http_headers({
                "Accept-Language": "en-US,en;q=0.9",
                "Accept-Encoding": "gzip, deflate, br",
                "Connection": "keep-alive",
            })
            result = await solve_turnstile_widget(
                page, url, sitekey, action, cdata, i + 1, session_id
            )
            await page.close()
            await asyncio.sleep(0.5)
          except Exception as e:
            err_str = str(e).split('\n')[0]
            print(f"{Fore.RED}❌ Widget {i+1} error: {err_str}{Style.RESET_ALL}")
            continue
      except Exception as e:
        err_str = str(e).split('\n')[0]
        print(f"{Fore.RED}❌ Browser error: {err_str}{Style.RESET_ALL}")
      finally:
        if context:
          try:
            await context.close()
          except Exception:
            pass
        await close_browser(driver, browser, config.debug)

      elapsed = time.time() - start_time
      queue_size = len(CONTINUOUS_TOKEN_QUEUES.get(session_id, []))
      print(
          f"{Fore.GREEN}✅ Batch {batch_count} completed in {elapsed:.2f}s |"
          f" Queue: {queue_size} tokens{Style.RESET_ALL}"
      )
      await asyncio.sleep(0.5)
    except Exception as e:
      err_str = str(e).split('\n')[0]
      print(f"{Fore.RED}❌ Continuous error: {err_str}{Style.RESET_ALL}")
      await asyncio.sleep(2)

  print(
      f"{Fore.RED}🛑 Continuous session {session_id[:8]} stopped{Style.RESET_ALL}"
  )


async def execute_on_demand_solve(
    url: str,
    sitekey: str,
    action: Optional[str] = None,
    cdata: Optional[str] = None,
    proxy_spec: Optional[dict] = None,
    timeout: int = 60,
    browser_type: str = "chrome",
    headless: bool = True,
    debug: bool = False,
) -> dict:
  start_time = time.time()
  config = BrowserConfig(
      browser_type=browser_type,
      headless=headless,
      useragent=None,
      proxy_support=bool(proxy_spec),
      debug=debug,
  )

  driver = None
  browser = None
  context = None
  page = None

  try:
    print(f"{Fore.CYAN}   [STEP 1] Launching stealth browser instance...{Style.RESET_ALL}")
    driver, browser = await launch_browser(config)
    
    print(f"{Fore.CYAN}   [STEP 2] Building browser context and applying proxy rules...{Style.RESET_ALL}")
    opts = context_options(config, proxy_spec)
    context = await browser.new_context(**opts)
    page = await context.new_page()

    print(f"{Fore.CYAN}   [STEP 3] Applying HTTP headers and fingerprint evasions...{Style.RESET_ALL}")
    await page.set_extra_http_headers({
        "Accept-Language": "en-US,en;q=0.9",
        "Accept-Encoding": "gzip, deflate, br",
        "Connection": "keep-alive",
    })

    user_agent = await page.evaluate("navigator.userAgent")
    print(f"{Fore.CYAN}   [STEP 4] Environment Ready. User-Agent: {user_agent[:50]}...{Style.RESET_ALL}")

    print(f"{Fore.CYAN}   [STEP 5] Connecting to target and intercepting Turnstile...{Style.RESET_ALL}")
    solve_coro = turnstile_solver.solve(page, url, sitekey, action, cdata)
    token, method = await asyncio.wait_for(solve_coro, timeout=float(timeout))
    elapsed = time.time() - start_time

    if not token:
      raise Exception("Turnstile challenge could not be resolved or was blocked.")

    site_name = re.sub(r"^https?://", "", url).split("/")[0].replace(".", "_")
    main_file = os.path.join(TOKENS_DIR, f"solvedtokens-{site_name}.txt")
    with open(main_file, "a", encoding="utf-8") as f:
      f.write(f"{token}\n")

    return {
        "status": "success",
        "token": token,
        "userAgent": user_agent,
        "elapsed": round(elapsed, 2),
        "method": method,
    }
  finally:
    if page:
      try:
        await page.close()
      except Exception:
        pass
    if context:
      try:
        await context.close()
      except Exception:
        pass
    await close_browser(driver, browser, debug)


def display_welcome() -> None:
  start_rainbow()
  _install_split_handler()


def create_app(config: BrowserConfig, threads: int = 4) -> Quart:
  app = Quart(__name__)
  app.secret_key = os.urandom(24)

  global_visible = not config.headless
  solve_semaphore = asyncio.Semaphore(threads)

  @app.before_serving
  async def startup() -> None:
    display_welcome()
    if not config.debug:
      logging.getLogger("hypercorn.access").disabled = True
    asyncio.create_task(_periodic_cleanup())
    logger.info(
        f"Ready: {config.browser_type}, "
        f"headless={'new' if config.headless else 'off (--no-headless)'}, "
        f"max concurrent={threads}"
    )

  @app.route("/", methods=["GET"])
  async def index():
    return await render_template(
        "dashboard.html", threads=threads, host=request.host
    )

  @app.route("/login", methods=["GET", "POST"])
  async def login():
    return redirect("/")

  @app.route("/logout")
  async def logout():
    return redirect("/")

  @app.route("/solve", methods=["POST"])
  async def solve_endpoint():
    req_data = await request.get_json()
    if not req_data:
      return jsonify({"status": "error", "error": "Missing JSON payload"}), 400

    url = req_data.get("url")
    sitekey = req_data.get("siteKey") or req_data.get("sitekey")
    mode = req_data.get("mode", "turnstile-min")
    timeout = int(req_data.get("timeout", 60))
    action = req_data.get("action")
    cdata = req_data.get("cdata")
    proxy_raw = req_data.get("proxy")
    residential = req_data.get("residential", False)

    if not url or not sitekey:
      return jsonify(
          {"status": "error", "error": "Both 'url' and 'siteKey' are required"}
      ), 400

    proxy_dict = parse_proxy_spec(proxy_raw)
    
    # Safely mask the proxy password for logging
    safe_proxy = "None"
    if proxy_dict:
      server = proxy_dict.get('server', '')
      user = proxy_dict.get('username', '')
      safe_proxy = f"{server}"
      if user:
        safe_proxy += f" (Auth: {user}:***)"

    print(f"\n{Fore.MAGENTA}================================================={Style.RESET_ALL}")
    print(f"{Fore.BLUE}[TASK START] Mode: {mode} | Target: {url}{Style.RESET_ALL}")
    print(f"{Fore.BLUE}[TASK INFO] Proxy: {safe_proxy} | Residential: {residential} | Timeout: {timeout}s{Style.RESET_ALL}")

    async with METRICS_LOCK:
      METRICS["in_flight"] += 1

    start_req_time = time.time()
    event_time_str = datetime.now().strftime("%H:%M:%S")

    try:
      async with solve_semaphore:
        result = await execute_on_demand_solve(
            url=url,
            sitekey=sitekey,
            action=action,
            cdata=cdata,
            proxy_spec=proxy_dict,
            timeout=timeout,
            browser_type=config.browser_type,
            headless=config.headless,
            debug=config.debug,
        )

      elapsed = round(time.time() - start_req_time, 2)
      print(f"{Fore.GREEN}[TASK SUCCESS] Token acquired in {elapsed}s!{Style.RESET_ALL}")
      print(f"{Fore.MAGENTA}=================================================\n{Style.RESET_ALL}")

      async with METRICS_LOCK:
        METRICS["solved"] += 1
        METRICS["latencies"].append(elapsed)
        if len(METRICS["latencies"]) > 500:
          METRICS["latencies"].pop(0)

        METRICS["recent_events"].insert(
            0,
            {
                "time": event_time_str,
                "mode": mode,
                "status": 200,
                "latency": f"{elapsed:.2f}s",
                "ok": True,
            },
        )
        if len(METRICS["recent_events"]) > 50:
          METRICS["recent_events"].pop()

      return jsonify({
          "status": result["status"],
          "token": result["token"],
          "userAgent": result["userAgent"]
      }), 200

    except asyncio.TimeoutError:
      elapsed = round(time.time() - start_req_time, 2)
      print(f"{Fore.RED}[TASK TIMEOUT] Execution exceeded {timeout}s! Proxy may be dead or connection too slow.{Style.RESET_ALL}")
      print(f"{Fore.MAGENTA}=================================================\n{Style.RESET_ALL}")
      
      async with METRICS_LOCK:
        METRICS["errors"] += 1
        METRICS["recent_events"].insert(
            0,
            {
                "time": event_time_str,
                "mode": mode,
                "status": 408,
                "latency": f"{elapsed:.2f}s",
                "ok": False,
            },
        )
        if len(METRICS["recent_events"]) > 50:
          METRICS["recent_events"].pop()

      return jsonify({
          "status": "error",
          "error": f"Resolution timed out after {timeout}s",
      }), 408

    except Exception as e:
      elapsed = round(time.time() - start_req_time, 2)
      err_str = str(e).split('\n')[0]
      print(f"{Fore.RED}[TASK FAILED] Error: {err_str}{Style.RESET_ALL}")
      print(f"{Fore.MAGENTA}=================================================\n{Style.RESET_ALL}")
      
      async with METRICS_LOCK:
        METRICS["errors"] += 1
        METRICS["recent_events"].insert(
            0,
            {
                "time": event_time_str,
                "mode": mode,
                "status": 500,
                "latency": f"{elapsed:.2f}s",
                "ok": False,
            },
        )
        if len(METRICS["recent_events"]) > 50:
          METRICS["recent_events"].pop()

      return jsonify({
          "status": "error",
          "error": err_str,
      }), 500

    finally:
      async with METRICS_LOCK:
        METRICS["in_flight"] = max(0, METRICS["in_flight"] - 1)

  @app.route("/api/metrics", methods=["GET"])
  async def api_metrics():
    async with METRICS_LOCK:
      solved = METRICS["solved"]
      errors = METRICS["errors"]
      in_flight = METRICS["in_flight"]
      lats = METRICS["latencies"]
      events = list(METRICS["recent_events"])

    total = solved + errors
    success_rate = round((solved / total) * 100, 1) if total > 0 else 100.0
    avg_latency = round(sum(lats) / len(lats), 2) if lats else 0.0

    if lats:
      sorted_l = sorted(lats)
      p95_idx = int(len(sorted_l) * 0.95)
      p95_latency = round(sorted_l[min(p95_idx, len(sorted_l) - 1)], 2)
    else:
      p95_latency = 0.0

    uptime_seconds = int(time.time() - SERVER_START_TIME)
    hours, remainder = divmod(uptime_seconds, 3600)
    minutes, _ = divmod(remainder, 60)
    uptime_str = f"{hours}h {minutes}m"

    return jsonify({
        "solved": solved,
        "errors": errors,
        "in_flight": in_flight,
        "success_rate": f"{success_rate}%",
        "avg_latency": f"{avg_latency:.2f}s",
        "p95_latency": f"{p95_latency:.2f}s",
        "uptime": uptime_str,
        "recent_events": events,
    })

  @app.route("/api/stats")
  async def api_stats():
    total_tokens = 0
    queue_size = 0
    active_sessions = 0
    for sid, session_data in CONTINUOUS_SESSIONS.items():
      if session_data.get("active", False):
        active_sessions += 1
        total_tokens += session_data.get("total_tokens", 0)
      if sid in CONTINUOUS_TOKEN_QUEUES:
        queue_size += len(CONTINUOUS_TOKEN_QUEUES[sid])
    return jsonify({
        "total_tokens": total_tokens,
        "queue_size": queue_size,
        "active_sessions": active_sessions,
        "threads": threads,
    })

  @app.route("/api/sessions")
  async def api_sessions():
    sessions = []
    for sid, session_data in CONTINUOUS_SESSIONS.items():
      sessions.append({
          "id": sid,
          "url": session_data.get("url", ""),
          "sitekey": session_data.get("sitekey", ""),
          "active": session_data.get("active", False),
          "total_tokens": session_data.get("total_tokens", 0),
          "queue_size": len(CONTINUOUS_TOKEN_QUEUES.get(sid, [])),
          "count": session_data.get("count", 5),
          "visible": session_data.get("visible", False),
          "created": session_data.get("created", 0),
      })
    return jsonify({"sessions": sessions})

  @app.route("/continuous", methods=["GET"])
  async def process_continuous():
    url = request.args.get("url")
    sitekey = request.args.get("sitekey")
    action = request.args.get("action")
    cdata = request.args.get("cdata")
    count = request.args.get("count", default=WIDGET_COUNT, type=int)
    visible = (
        request.args.get("visible", default="false", type=str).lower() == "true"
    )

    if not url or not sitekey:
      return (
          jsonify({
              "errorId": 1,
              "errorCode": "ERROR_WRONG_PAGEURL",
              "errorDescription": "Both 'url' and 'sitekey' are required",
          }),
          200,
      )

    session_id = str(uuid.uuid4())
    use_visible = visible or global_visible

    CONTINUOUS_SESSIONS[session_id] = {
        "active": True,
        "url": url,
        "sitekey": sitekey,
        "created": time.time(),
        "count": count,
        "total_tokens": 0,
        "visible": use_visible,
    }
    CONTINUOUS_TOKEN_QUEUES[session_id] = []

    asyncio.create_task(
        solve_continuous_widgets(
            url, sitekey, action, cdata, session_id, count, not use_visible
        )
    )

    return (
        jsonify({
            "errorId": 0,
            "session_id": session_id,
            "message": (
                f"Continuous solving started (no delay, visible={use_visible})"
            ),
            "widget_count": count,
            "visible": use_visible,
            "queue": "/result?id=" + session_id,
            "status": "/queue/status?id=" + session_id,
            "stop": "/stop?id=" + session_id,
        }),
        200,
    )

  @app.route("/result", methods=["GET"])
  async def get_result():
    session_id = request.args.get("id")
    if not session_id:
      return (
          jsonify({
              "errorId": 1,
              "errorCode": "ERROR_WRONG_CAPTCHA_ID",
              "errorDescription": "Session ID required",
          }),
          200,
      )

    if session_id not in CONTINUOUS_TOKEN_QUEUES:
      return (
          jsonify({
              "errorId": 1,
              "errorCode": "ERROR_WRONG_CAPTCHA_ID",
              "errorDescription": "Invalid session ID",
          }),
          200,
      )

    queue = CONTINUOUS_TOKEN_QUEUES[session_id]
    if not queue:
      return (
          jsonify({
              "status": "empty",
              "message": "No tokens available. Please wait.",
              "queue_size": 0,
          }),
          200,
      )

    token_data = queue.pop(0)
    if session_id in CONTINUOUS_SESSIONS:
      CONTINUOUS_SESSIONS[session_id]["total_tokens"] = len(queue)

    return (
        jsonify({
            "errorId": 0,
            "status": "ready",
            "token": token_data["token"],
            "elapsed": token_data["elapsed"],
            "widget_id": token_data["widget_id"],
            "timestamp": token_data["timestamp"],
            "queue_remaining": len(queue),
        }),
        200,
    )

  @app.route("/queue/status", methods=["GET"])
  async def get_queue_status():
    session_id = request.args.get("id")
    if not session_id:
      return (
          jsonify({
              "errorId": 1,
              "errorDescription": "Session ID required",
          }),
          200,
      )

    if session_id not in CONTINUOUS_TOKEN_QUEUES:
      return (
          jsonify({
              "errorId": 1,
              "errorDescription": "Invalid session ID",
          }),
          200,
      )

    queue = CONTINUOUS_TOKEN_QUEUES[session_id]
    session_data = CONTINUOUS_SESSIONS.get(session_id, {})
    return (
        jsonify({
            "session_id": session_id,
            "active": session_data.get("active", False),
            "queue_size": len(queue),
            "total_tokens": session_data.get("total_tokens", 0),
            "url": session_data.get("url"),
            "widget_count": session_data.get("count"),
            "visible": session_data.get("visible", False),
            "created": session_data.get("created"),
            "next_token": queue[0] if queue else None,
        }),
        200,
    )

  @app.route("/stop", methods=["GET"])
  async def stop_continuous():
    session_id = request.args.get("id")
    if not session_id:
      return (
          jsonify({
              "errorId": 1,
              "errorDescription": "Session ID required",
          }),
          200,
      )

    if session_id not in CONTINUOUS_SESSIONS:
      return (
          jsonify({
              "errorId": 1,
              "errorDescription": "Invalid session ID",
          }),
          200,
      )

    CONTINUOUS_SESSIONS[session_id]["active"] = False
    remaining = 0
    if session_id in CONTINUOUS_TOKEN_QUEUES:
      remaining = len(CONTINUOUS_TOKEN_QUEUES[session_id])

    return (
        jsonify({
            "errorId": 0,
            "message": f"Session {session_id[:8]} stopped",
            "remaining_tokens": remaining,
        }),
        200,
    )

  return app


async def _periodic_cleanup() -> None:
  while True:
    try:
      await asyncio.sleep(CLEANUP_INTERVAL_S)
      for sid in list(CONTINUOUS_SESSIONS.keys()):
        if time.time() - CONTINUOUS_SESSIONS[sid]["created"] > TASK_TTL_S:
          if not CONTINUOUS_SESSIONS[sid].get("active", False):
            del CONTINUOUS_SESSIONS[sid]
            if sid in CONTINUOUS_TOKEN_QUEUES:
              del CONTINUOUS_TOKEN_QUEUES[sid]
      for sid in list(ACTIVE_SESSIONS.keys()):
        if time.time() - ACTIVE_SESSIONS[sid]["created"] > 3600:
          api_key = ACTIVE_SESSIONS[sid].get("api_key")
          if api_key and api_key in API_KEYS:
            del API_KEYS[api_key]
          del ACTIVE_SESSIONS[sid]
    except Exception as e:
      logger.error(f"Error during cleanup: {e}")


def parse_args() -> argparse.Namespace:
  parser = argparse.ArgumentParser(
      description="HudSolver - Continuous Queue Solver & Direct API"
  )
  parser.add_argument(
      "--no-headless",
      action="store_true",
      help="Show browser (visible mode)",
  )
  parser.add_argument(
      "--headless",
      action="store_true",
      default=True,
      help="Run in headless mode (default)",
  )
  parser.add_argument("--useragent", type=str, help="Custom User-Agent")
  parser.add_argument("--debug", action="store_true")
  parser.add_argument("--browser_type", type=str, default="chrome")
  parser.add_argument("--thread", type=int, default=4)
  parser.add_argument("--proxy", action="store_true")
  parser.add_argument("--host", type=str, default="0.0.0.0")
  parser.add_argument("--port", type=str, default="4040")
  return parser.parse_args()


def _kill_child_processes() -> None:
  try:
    import psutil

    for child in psutil.Process(os.getpid()).children(recursive=True):
      try:
        child.kill()
      except Exception:
        pass
  except Exception:
    pass


def main() -> None:
  args = parse_args()
  if args.browser_type not in ("chromium", "chrome", "msedge", "camoufox"):
    logger.error(f"Unknown browser type: {args.browser_type}")
    return

  headless_mode = args.headless and not args.no_headless

  config = BrowserConfig(
      browser_type=args.browser_type,
      headless=headless_mode,
      useragent=args.useragent,
      proxy_support=args.proxy,
      debug=args.debug,
  )
  app = create_app(config, threads=args.thread)

  def emergency_shutdown(sig, frame):
    stop_rainbow()
    sys.__stdout__.write("\033[0m\n⚠️ Shutting down...\n")
    sys.__stdout__.flush()
    _kill_child_processes()
    os._exit(0)

  signal.signal(signal.SIGINT, emergency_shutdown)
  signal.signal(signal.SIGTERM, emergency_shutdown)

  try:
    app.run(host=args.host, port=int(args.port))
  except KeyboardInterrupt:
    emergency_shutdown(None, None)


if __name__ == "__main__":
  main()