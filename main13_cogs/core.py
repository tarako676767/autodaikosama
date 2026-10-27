import os
import re
import copy
import base64
import gzip
import json
import uuid
import secrets
import hashlib
import hmac
import threading
import traceback
import time
import asyncio
import logging
import random
import sys
import functools
import sqlite3
import urllib.parse
import discord
from discord import ui
from discord.ext import commands
from discord import app_commands
import requests
from bs4 import BeautifulSoup
from dotenv import load_dotenv
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from DISCORD.discord_log import send_usage_log

load_dotenv()

# =====================
# プロキシ設定（全通信共通）
# =====================
PROXY_URL = os.getenv("PROXY_URL", "").strip()
PROXIES = {"http": PROXY_URL, "https": PROXY_URL} if PROXY_URL else {}
if PROXY_URL:
    os.environ["HTTP_PROXY"] = PROXY_URL
    os.environ["HTTPS_PROXY"] = PROXY_URL
    os.environ["http_proxy"] = PROXY_URL
    os.environ["https_proxy"] = PROXY_URL

# ── requests.Session を継承してプロキシを強制注入 ──
import functools as _ft
_orig_requests_Session = requests.Session
class _ProxiedRequestsSession(_orig_requests_Session):
    def __init__(self, *a, **kw):
        super().__init__(*a, **kw)
        self.proxies.update(PROXIES)
requests.Session = _ProxiedRequestsSession

# ── requests モジュールレベル関数にもプロキシを強制付与 ──
for _mn in ("get", "post", "put", "patch", "delete", "head", "options", "request"):
    _orig_fn = getattr(requests, _mn)
    def _make_proxied(fn):
        @_ft.wraps(fn)
        def _wrapped(*a, **kw):
            kw.setdefault("proxies", PROXIES)
            return fn(*a, **kw)
        return _wrapped
    setattr(requests, _mn, _make_proxied(_orig_fn))

# ── urllib.request グローバル opener にプロキシを強制設定 ──
import urllib.request as _urllib_req
_urllib_proxy_handler = _urllib_req.ProxyHandler(PROXIES)
_urllib_req.install_opener(_urllib_req.build_opener(_urllib_proxy_handler))

# プロキシ疎通確認（外部通信を伴うため明示有効時のみ）
if PROXY_URL and os.getenv("PROXY_CHECK_ON_STARTUP", "0") == "1":
    try:
        _r = requests.get("https://httpbin.org/ip", proxies=PROXIES, timeout=10)
        if _r.status_code == 200:
            print(f"[PROXY CHECK] OK - 外部IP: {_r.json()['origin']}")
        else:
            print(f"[PROXY CHECK] FAILED - HTTPステータス: {_r.status_code}")
    except Exception as _e:
        print(f"[PROXY CHECK] FAILED - {type(_e).__name__}")
elif not PROXY_URL:
    print("[PROXY CHECK] SKIPPED - PROXY_URLが未設定です")

# =====================
# 設定値
# =====================
MAX_API_KEYS = 5000          # api_keys 辞書の上限
API_KEY_TTL = 600            # APIキーの有効期間(秒)
MAX_WORKERS = 10              # ジョブ実行ワーカー数
MAX_INFLIGHT_JOBS = 30       # 同時に受け付ける未完了ジョブ数
JOB_TIMEOUT = 300            # 進捗が更新されないジョブのタイムアウト(秒)
JOB_ABSOLUTE_TIMEOUT = 600   # 進捗が続いていても待つ絶対上限(秒)
CLONE_JOB_TIMEOUT = 600      # 複製中の連続した認証・保存通信は最大10分待つ
CLONE_JOB_ABSOLUTE_TIMEOUT = 1800  # 複数コピーの連続通信を考慮して30分
MAX_CHAR_LIST = 300          # char_list の最大要素数
MAX_CHARACTER_SETTINGS = 1000  # レアリティ単位・全871体の名前選択に対応
MAX_COUNT = 5                # 作成/複製の最大個数
MAX_LEGEND_SELECTIONS = 5000 # レジェンド系の章/星/ステージ選択数上限

# にゃんこ大戦争 JP 15.5.1。通信・新規作成・複製・ゲームデータ参照で
# 別々の値を使うと、新キャラ枠や第四形態の判定が旧版へ戻るため一元管理する。
TARGET_GAME_VERSION_NUMBER = 150501

# 通常ページから非表示にするだけでなく、APIへ直接送られてもVIP確認なしでは適用しない。
VIP_ONLY_SYSTEM_ACTIONS = {
    "user_rank_rewards_claimed",
    "user_rank_rewards_unclaimed",
    "catguide_rewards_claimed",
    "catguide_rewards_unclaimed",
    "cat_scratcher_reset",
    "all_missions_clear",
    "labyrinth_medals",
    "ototo_detailed",
    "dojo_score_detailed",
    "future_score_detailed",
}

# =====================
# =====================
DISCORD_BOT_TOKEN = os.getenv("DISCORD_BOT_TOKEN", "")

def _positive_env_int(name, fallback):
    try:
        value = int(os.getenv(name, str(fallback)))
        return value if 1 <= value <= 1_000_000 else fallback
    except (TypeError, ValueError):
        return fallback


VIP_PLAN_PRICES = {
    30: _positive_env_int("VIP_PRICE_30", 300),
    60: _positive_env_int("VIP_PRICE_60", 600),
    90: _positive_env_int("VIP_PRICE_90", 900),
}
VIP_PRICE_LABEL = f"30日{VIP_PLAN_PRICES[30]:,}円から"
VIP_PLAN_LABEL = os.getenv("VIP_PLAN_LABEL", "VIPプラン").strip() or "VIPプラン"

DISCORD_API = "https://discord.com/api"

# =====================
# 入力フォーマット定義
# =====================
TRANSFER_CODE_RE = re.compile(r'^[0-9a-fA-F]{9}$')
AUTH_CODE_RE = re.compile(r'^\d{4}$')
# 「時間:分」形式のみ許可。時間は最大4桁(9999まで)、分は0〜59のみ。
PLAYTIME_RE = re.compile(r'^(\d{1,4}):([0-5]?\d)$')
OPERATION_ID_RE = re.compile(r'^[A-Za-z0-9]{30}$')
ADMIN_SNAPSHOT_KEY = os.getenv("ADMIN_SNAPSHOT_KEY", "").strip()


def validate_playtime_str(value):
    """'時間:分' 形式のみ許可。不正なら None、OKなら (hours, minutes) のタプルを返す。"""
    if not isinstance(value, str):
        return None
    m = PLAYTIME_RE.match(value.strip())
    if not m:
        return None
    hours, minutes = int(m.group(1)), int(m.group(2))
    if hours > 9999 or minutes > 59:
        return None
    return hours, minutes


def safe_custom_playtime(data):
    """custom_playtime を検証済みの文字列として返す。不正・未指定なら空文字。"""
    raw = data.get("custom_playtime", "")
    if raw in (None, ""):
        return ""
    raw_str = str(raw).strip()
    return raw_str if validate_playtime_str(raw_str) else ""


# =====================
# APIキー管理
# =====================
def generate_api_key():
    key = str(uuid.uuid4())
    with _job_db_connect() as conn:
        conn.execute(
            "INSERT INTO api_request_keys(api_key,created_at,used) VALUES(?,?,0)",
            (key, time.time()),
        )
        conn.execute(
            "DELETE FROM api_request_keys WHERE api_key IN "
            "(SELECT api_key FROM api_request_keys ORDER BY created_at DESC LIMIT -1 OFFSET ?)",
            (MAX_API_KEYS,),
        )
    return key


def validate_and_consume_api_key(key: str) -> bool:
    with _job_db_connect() as conn:
        cur = conn.execute(
            "UPDATE api_request_keys SET used=1 "
            "WHERE api_key=? AND used=0 AND created_at>=?",
            (str(key), time.time() - API_KEY_TTL),
        )
    return cur.rowcount == 1


def cleanup_api_keys():
    while True:
        time.sleep(60)
        with _job_db_connect() as conn:
            conn.execute(
                "DELETE FROM api_request_keys WHERE created_at < ? OR used=1",
                (time.time() - API_KEY_TTL,),
            )


try:
    from bcsfe import core
    from bcsfe.core.server.server_handler import ServerHandler
    from bcsfe.core.game.catbase.cat import Talent
    from bcsfe.core.game.catbase.user_rank_rewards import Reward
    from bcsfe.core.game.catbase.playtime import PlayTime
    from bcsfe.core.game.map.outbreaks import (
        Outbreak as ZombieOutbreak,
        Chapter as ZombieChapter,
    )
except ImportError:
    import core
    from core.server.server_handler import ServerHandler

# BCSFE 3.6.0は保存ファイルのアップロードだけタイムアウトなしで、その他は
# 既定30秒。複製では保存回数が増えるため、接続15秒・通常45秒・保存90秒の
# 上限を明示する。TimeoutもConnectionErrorと同様にNoneへ変換し、BCSFE側の
# 安全な段階別失敗処理へ戻す。
def _bounded_timeout_env(name: str, default: int, minimum: int, maximum: int) -> int:
    try:
        return max(minimum, min(maximum, int(os.getenv(name, str(default)))))
    except (TypeError, ValueError):
        return default


BCSFE_CONNECT_TIMEOUT = _bounded_timeout_env("BCSFE_CONNECT_TIMEOUT", 15, 5, 60)
BCSFE_API_TIMEOUT = _bounded_timeout_env("BCSFE_API_TIMEOUT", 45, 15, 120)
BCSFE_UPLOAD_TIMEOUT = _bounded_timeout_env("BCSFE_UPLOAD_TIMEOUT", 90, 30, 300)


def _bounded_bcsfe_request_post(self, no_timeout=False):
    read_timeout = BCSFE_UPLOAD_TIMEOUT if self.form is not None else BCSFE_API_TIMEOUT
    try:
        return requests.post(
            self.url,
            headers=self.headers,
            data=self.data.data,
            timeout=(BCSFE_CONNECT_TIMEOUT, read_timeout),
            files=None if self.form is None else self.form.into_files(),
        )
    except (requests.exceptions.ConnectionError, requests.exceptions.Timeout) as exc:
        print(f"[BCSFE NETWORK] POST failed: {type(exc).__name__}")
        return None


core.RequestHandler.post = _bounded_bcsfe_request_post

core.core_data.init_data()

TARGET_GAME_VERSION = core.GameVersion(TARGET_GAME_VERSION_NUMBER)
BCSFE_EDIT_LOCK = threading.RLock()

# =====================
# ジョブ実行プール
# =====================
executor = ThreadPoolExecutor(max_workers=MAX_WORKERS)

jobs: dict = {}
jobs_lock = threading.Lock()
JOBS_MAX = 200
JOBS_TTL = 60 * 30
OPERATION_RETENTION = 2 * 24 * 60 * 60  # 受付IDと失敗セーブは48時間で失効

# =====================
# 使用回数カウンター（代行・作成・複製の成功回数を全種合算。count.dbに永続化し再起動後も保持）
# =====================
import sqlite3

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
BACKUP_DIR = os.path.join(BASE_DIR, "BACKUP")
os.makedirs(BACKUP_DIR, mode=0o700, exist_ok=True)
try:
    os.chmod(BACKUP_DIR, 0o700)
except OSError:
    pass
USAGE_DB_PATH = os.path.join(BASE_DIR, "count.db")
try:
    if os.path.exists(USAGE_DB_PATH):
        os.chmod(USAGE_DB_PATH, 0o600)
except OSError:
    pass
OPERATION_DB_PATH = os.path.join(BACKUP_DIR, "admin_recovery.db")
BONUS_DB_PATH = os.path.join(BASE_DIR, "Login", "Bonus.db")
ACCOUNT_DB_PATH = os.path.join(BASE_DIR, "ACCOUNT", "account.db")
usage_count_lock = threading.Lock()

_identity_secret = os.getenv("IDENTITY_HASH_KEY") or os.getenv("FLASK_SECRET_KEY")
if not _identity_secret:
    # FLASK_SECRET_KEY未設定時の開発用フォールバック。本番では再起動をまたいで
    # 同じ利用者を識別できるよう、必ずいずれかの環境変数を固定する。
    _identity_secret = secrets.token_hex(32)
    print("[WARNING] IDENTITY_HASH_KEY/FLASK_SECRET_KEY is not configured; identity hashes may change after restart.")


def _usage_db_connect():
    conn = sqlite3.connect(USAGE_DB_PATH, timeout=10, check_same_thread=False)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS usage_count (
            id INTEGER PRIMARY KEY CHECK (id = 1),
            count INTEGER NOT NULL DEFAULT 0
        )
    """)
    conn.execute("INSERT OR IGNORE INTO usage_count (id, count) VALUES (1, 0)")
    conn.commit()
    return conn


_usage_db_conn = _usage_db_connect()
try:
    os.chmod(USAGE_DB_PATH, 0o600)
except OSError:
    pass


# ジョブ状態はメモリだけだと、Gunicorn等の別ワーカーに
# /api/job が割り当てられた時やワーカー再起動後に404になる。
# count.db内にJSONとして保存し、プロセス間で共有する。
@contextmanager
def _job_db_connect():
    conn = sqlite3.connect(USAGE_DB_PATH, timeout=10, check_same_thread=False)
    try:
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("""
            CREATE TABLE IF NOT EXISTS background_jobs (
                job_id TEXT PRIMARY KEY,
                status TEXT NOT NULL,
                payload TEXT NOT NULL,
                created_at REAL NOT NULL,
                updated_at REAL NOT NULL
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS api_request_keys (
                api_key TEXT PRIMARY KEY,
                created_at REAL NOT NULL,
                used INTEGER NOT NULL DEFAULT 0
            )
        """)
        conn.commit()
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


with _job_db_connect() as _job_init_conn:
    pass


@contextmanager
def _operation_db_connect():
    conn = sqlite3.connect(OPERATION_DB_PATH, timeout=10, check_same_thread=False)
    try:
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("""
            CREATE TABLE IF NOT EXISTS operation_records (
                operation_id TEXT PRIMARY KEY,
                job_id TEXT NOT NULL UNIQUE,
                operation_type TEXT NOT NULL,
                status TEXT NOT NULL,
                error TEXT,
                recovery_status TEXT NOT NULL DEFAULT 'not_needed',
                snapshot BLOB,
                reissue_result BLOB,
                created_at REAL NOT NULL,
                updated_at REAL NOT NULL
            )
        """)
        columns = {row[1] for row in conn.execute("PRAGMA table_info(operation_records)")}
        if "reissue_result" not in columns:
            conn.execute("ALTER TABLE operation_records ADD COLUMN reissue_result BLOB")
        conn.commit()
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


with _operation_db_connect() as _operation_init_conn:
    pass
try:
    os.chmod(OPERATION_DB_PATH, 0o600)
except OSError:
    pass

threading.Thread(target=cleanup_api_keys, daemon=True).start()


def _persist_job(job_id: str, job: dict):
    payload = json.dumps(job, ensure_ascii=False, separators=(",", ":"))
    created_at = float(job.get("created_at", time.time()))
    updated_at = float(job.get("updated_at", created_at))
    with _job_db_connect() as conn:
        conn.execute(
            """INSERT INTO background_jobs(job_id,status,payload,created_at,updated_at)
               VALUES(?,?,?,?,?)
               ON CONFLICT(job_id) DO UPDATE SET
                 status=excluded.status,payload=excluded.payload,
                 created_at=excluded.created_at,updated_at=excluded.updated_at""",
            (job_id, str(job.get("status", "pending")), payload, created_at, updated_at),
        )


def _load_job(job_id: str):
    with _job_db_connect() as conn:
        row = conn.execute(
            "SELECT payload FROM background_jobs WHERE job_id = ?", (job_id,)
        ).fetchone()
    if not row:
        return None
    try:
        value = json.loads(row[0])
        return value if isinstance(value, dict) else None
    except (TypeError, ValueError):
        return None


def _create_job(job_id: str, job: dict):
    with jobs_lock:
        jobs[job_id] = job
    _persist_job(job_id, job)


def _create_operation(operation_id: str, job_id: str, operation_type: str, now: float):
    with _operation_db_connect() as conn:
        conn.execute(
            """INSERT INTO operation_records(
                   operation_id,job_id,operation_type,status,error,recovery_status,
                   snapshot,reissue_result,created_at,updated_at
               ) VALUES(?,?,?,?,?,?,?,?,?,?)""",
            (operation_id, job_id, operation_type, "pending", None, "not_needed", None, None, now, now),
        )


def _update_operation(operation_id: str, **changes):
    allowed = {"status", "error", "recovery_status", "snapshot", "reissue_result", "updated_at"}
    values = {key: value for key, value in changes.items() if key in allowed}
    if not values:
        return
    values.setdefault("updated_at", time.time())
    assignments = ",".join(f"{key}=?" for key in values)
    with _operation_db_connect() as conn:
        conn.execute(
            f"UPDATE operation_records SET {assignments} WHERE operation_id=?",
            (*values.values(), operation_id),
        )


def _load_operation(operation_id: str):
    with _operation_db_connect() as conn:
        row = conn.execute(
            """SELECT operation_id,job_id,operation_type,status,error,recovery_status,
                      snapshot,reissue_result,created_at,updated_at
               FROM operation_records WHERE operation_id=?""",
            (operation_id,),
        ).fetchone()
    if not row:
        return None
    keys = ("operation_id", "job_id", "operation_type", "status", "error",
            "recovery_status", "snapshot", "reissue_result", "created_at", "updated_at")
    record = dict(zip(keys, row))
    if time.time() >= float(record["created_at"]) + OPERATION_RETENTION:
        with _operation_db_connect() as conn:
            conn.execute("DELETE FROM operation_records WHERE operation_id=?", (operation_id,))
        return None
    return record


def _close_operation(
    operation_id: str,
    *,
    status: str,
    recovery_status: str,
    error: str | None = None,
    issued_codes: tuple[str, str] | None = None,
):
    """Close an operation without making an already-issued ID disappear.

    Closed records contain no save snapshot. When a code was already issued, an
    encrypted copy is retained for the admin panel until the normal 48-hour
    cleanup. Keeping the row distinguishes an expired/unknown ID from an
    operation that never reached the recoverable stage.
    """
    if not operation_id:
        return
    encrypted_codes = None
    if issued_codes:
        try:
            encrypted_codes = _encrypt_snapshot(
                json.dumps(
                    {"tc": issued_codes[0], "ac": issued_codes[1]},
                    separators=(",", ":"),
                ).encode(),
                operation_id,
            )
        except Exception as exc:
            # Do not discard an existing save snapshot when the fallback code
            # itself cannot be stored. The admin panel can still reissue it.
            combined = _safe_error_message(
                f"{error or ''}\n発行済みコードの保管に失敗: {exc}"
            )
            _update_operation(
                operation_id,
                status="error",
                error=combined,
                recovery_status="reissue_failed",
            )
            return
    _update_operation(
        operation_id,
        status=status,
        error=_safe_error_message(error) if error else None,
        recovery_status=recovery_status,
        snapshot=None,
        reissue_result=encrypted_codes,
    )


def _operation_public(record: dict):
    status_labels = {
        "pending": "受付済み",
        "running": "処理中",
        "done": "完了",
        "error": "エラー",
    }
    recovery_labels = {
        "not_needed": "復旧不要",
        "not_available": "セーブ未取得のため再発行不可",
        "snapshot_saved": "管理者による再発行が可能",
        "reissue_failed": "再発行待ち",
        "issuing": "再発行中",
        "client_code_issued": "引き継ぎコード発行済み",
        "admin_reissued": "引き継ぎコード再発行済み",
    }
    return {
        "operation_id": record["operation_id"],
        "operation_type": record["operation_type"],
        "status": record["status"],
        "error": record.get("error"),
        "recovery_status": record.get("recovery_status", "not_needed"),
        "status_label": status_labels.get(record["status"], record["status"]),
        "recovery_status_label": recovery_labels.get(
            record.get("recovery_status", "not_needed"),
            record.get("recovery_status", "not_needed"),
        ),
        "created_at": record["created_at"],
        "updated_at": record["updated_at"],
        "can_reissue": bool(
            record.get("snapshot")
            and record.get("status") == "error"
            and record.get("recovery_status") in ("snapshot_saved", "reissue_failed")
        ),
        "expires_at": record["created_at"] + OPERATION_RETENTION,
    }


def _snapshot_cipher_key() -> bytes:
    # 専用鍵を優先。未設定時は複数ワーカーで同じFLASK_SECRET_KEYから導出する。
    source = ADMIN_SNAPSHOT_KEY or os.getenv("FLASK_SECRET_KEY", "")
    if not source:
        raise RuntimeError("ADMIN_SNAPSHOT_KEY または FLASK_SECRET_KEY が必要です")
    return hashlib.sha256((source + "|autocat-admin-snapshot-v1").encode()).digest()


def _encrypt_snapshot(data: bytes, operation_id: str) -> bytes:
    key = _snapshot_cipher_key()
    nonce = secrets.token_bytes(12)
    aad = ("autocat-admin-snapshot-v2|" + operation_id).encode()
    return b"ACS2" + nonce + AESGCM(key).encrypt(nonce, data, aad)


def _decrypt_snapshot(blob: bytes, operation_id: str) -> bytes:
    if not blob or not blob.startswith(b"ACS2") or len(blob) < 32:
        raise ValueError("保存データが不正です")
    key = _snapshot_cipher_key()
    nonce, ciphertext = blob[4:16], blob[16:]
    aad = ("autocat-admin-snapshot-v2|" + operation_id).encode()
    try:
        return AESGCM(key).decrypt(nonce, ciphertext, aad)
    except Exception as exc:
        raise ValueError("保存データの検証に失敗しました") from exc


def _save_operation_snapshot(operation_id: str, save_file):
    raw = save_file.to_data().to_bytes()
    snapshot = _encrypt_snapshot(gzip.compress(raw, compresslevel=6), operation_id)
    _update_operation(operation_id, snapshot=snapshot, recovery_status="snapshot_saved")


def _generate_operation_id() -> str:
    alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
    return "".join(secrets.choice(alphabet) for _ in range(30))


def _safe_operation_id(data: dict) -> str:
    value = str(data.get("operation_id", "")).strip()
    if not value:
        return _generate_operation_id()
    return value if OPERATION_ID_RE.fullmatch(value) else ""


def _safe_error_message(value) -> str:
    text = str(value or "処理に失敗しました。")[:2000]
    text = re.sub(r"(https?://)[^\s/@:]+:[^\s/@]+@", r"\1***:***@", text)
    text = re.sub(r"(?i)(authorization|token|secret|password)\s*[:=]\s*[^\s,;]+", r"\1=***", text)
    return text


def _update_job(job_id: str, changes: dict):
    """Update the local cache and durable shared job record together."""
    with jobs_lock:
        job = jobs.get(job_id)
        if job is None:
            job = _load_job(job_id)
            if job is None:
                return
            jobs[job_id] = job
        job.update(changes)
        snapshot = copy.deepcopy(job)
    _persist_job(job_id, snapshot)




def get_usage_count() -> int:
    with usage_count_lock:
        row = _usage_db_conn.execute("SELECT count FROM usage_count WHERE id = 1").fetchone()
        return row[0] if row else 0


def increment_usage_count() -> int:
    with usage_count_lock:
        _usage_db_conn.execute("UPDATE usage_count SET count = count + 1 WHERE id = 1")
        _usage_db_conn.commit()
        row = _usage_db_conn.execute("SELECT count FROM usage_count WHERE id = 1").fetchone()
        return row[0] if row else 0


def count_inflight_jobs() -> int:
    with _job_db_connect() as conn:
        row = conn.execute(
            "SELECT COUNT(*) FROM background_jobs WHERE status IN ('pending','running')"
        ).fetchone()
    return int(row[0]) if row else 0


def cleanup_jobs():
    while True:
        time.sleep(30)
        now = time.time()
        with _job_db_connect() as conn:
            rows = conn.execute(
                "SELECT job_id,payload,updated_at FROM background_jobs "
                "WHERE status IN ('pending','running')"
            ).fetchall()
        for jid, raw_payload, stored_updated_at in rows:
            try:
                job = json.loads(raw_payload)
            except (TypeError, ValueError):
                continue
            created = float(job.get("created_at", now))
            last_activity = float(job.get("updated_at") or job.get("started_at") or created)
            absolute_timeout = (
                CLONE_JOB_ABSOLUTE_TIMEOUT
                if job.get("operation_type") == "clone"
                else JOB_ABSOLUTE_TIMEOUT
            )
            inactivity_timeout = (
                CLONE_JOB_TIMEOUT
                if job.get("operation_type") == "clone"
                else JOB_TIMEOUT
            )
            if now - last_activity > inactivity_timeout or now - created > absolute_timeout:
                job.update({"status": "error", "updated_at": now})
                if job.get("transfer_received"):
                    job["error"] = (
                        "引き継ぎ取得後に処理がタイムアウトしました。"
                        "同じ操作を再実行せず、管理者へ確認してください。"
                    )
                else:
                    job["error"] = "処理がタイムアウトしました。もう一度実行してください。"
                # 読み取り後にワーカーが進捗更新した場合はタイムアウトで上書きしない。
                with _job_db_connect() as conn:
                    cur = conn.execute(
                        "UPDATE background_jobs SET status=?,payload=?,updated_at=? "
                        "WHERE job_id=? AND updated_at=?",
                        ("error", json.dumps(job, ensure_ascii=False, separators=(",", ":")),
                         now, jid, stored_updated_at),
                    )
                if cur.rowcount:
                    with jobs_lock:
                        jobs[jid] = job
                    _settle_job_quota(job)
                    operation_id = job.get("operation_id")
                    if operation_id:
                        if job.get("return_pending"):
                            job["admin_recovery_required"] = True
                            _update_job(jid, {
                                "admin_recovery_required": True,
                                "return_pending": False,
                            })
                            _update_operation(
                                operation_id, status="error", error=job["error"],
                                recovery_status="reissue_failed",
                            )
                        elif job.get("recovery_transfer_code"):
                            # A usable return code wins over a stale timeout flag.
                            # Clear the flag and retain a closed record so history
                            # never points at an immediately deleted operation.
                            job["admin_recovery_required"] = False
                            _update_job(jid, {"admin_recovery_required": False})
                            _close_operation(
                                operation_id,
                                status="error",
                                recovery_status="client_code_issued",
                                error=job["error"],
                                issued_codes=(
                                    job["recovery_transfer_code"],
                                    job.get("recovery_auth_code") or "",
                                ),
                            )
                        else:
                            job["admin_recovery_required"] = True
                            _update_job(jid, {"admin_recovery_required": True})
                            operation = _load_operation(operation_id)
                            recovery_state = (
                                operation.get("recovery_status", "reissue_failed")
                                if operation and operation.get("snapshot") else "reissue_failed"
                            )
                            _update_operation(
                                operation_id, status="error", error=job["error"],
                                recovery_status=recovery_state,
                            )

        cutoff = now - JOBS_TTL
        with _job_db_connect() as conn:
            conn.execute(
                "DELETE FROM background_jobs WHERE status IN ('done','error') AND created_at < ?",
                (cutoff,),
            )
            keep_ids = {
                row[0] for row in conn.execute(
                    "SELECT job_id FROM background_jobs ORDER BY created_at DESC LIMIT ?", (JOBS_MAX,)
                ).fetchall()
            }
            if keep_ids:
                placeholders = ",".join("?" for _ in keep_ids)
                conn.execute(
                    f"DELETE FROM background_jobs WHERE job_id NOT IN ({placeholders})",
                    tuple(keep_ids),
                )
        with jobs_lock:
            for jid in list(jobs):
                if jid not in keep_ids:
                    jobs.pop(jid, None)
        # 返却コード発行まで失敗した操作だけを残し、作成から48時間で削除。
        with _operation_db_connect() as conn:
            conn.execute(
                "DELETE FROM operation_records WHERE created_at < ?",
                (now - OPERATION_RETENTION,),
            )


threading.Thread(target=cleanup_jobs, daemon=True).start()


def _new_job_access_token() -> tuple[str, str]:
    token = secrets.token_urlsafe(32)
    return token, hashlib.sha256(token.encode()).hexdigest()


# =====================
# Discordログイン（チャット・管理者）/ サイトアカウント（VIP）
# =====================


# =====================
# 入力バリデーション
# =====================


def safe_count(data, maximum=MAX_COUNT):
    maximum = max(1, min(MAX_COUNT, int(maximum)))
    try:
        return max(1, min(maximum, int(data.get("count", 1))))
    except (TypeError, ValueError):
        return 1


def safe_character_settings(data):
    """名前選択UIから届いたキャラ・形態・レベル設定を安全な範囲へ丸める。IDは画面表示と同じ1始まり。"""
    out = []
    seen = set()
    try:
        form_counts = {
            character["id"]: character["form_count"]
            for character in get_character_metadata().get("characters", [])
            if character.get("selectable", True)
        }
    except Exception:
        form_counts = {}
    for raw in data.get("character_settings", [])[:MAX_CHARACTER_SETTINGS]:
        try:
            cat_id = max(1, min(9999, int(raw.get("id"))))
            if form_counts and cat_id not in form_counts:
                continue
            max_form = form_counts.get(cat_id, 4)
            form = max(1, min(max_form, int(raw.get("form", 1))))
            base_level = max(1, min(60, int(raw.get("base_level", 60))))
            plus_level = max(0, min(90, int(raw.get("plus_level", 0))))
            level_mode = raw.get("level_mode", "individual")
            if level_mode not in {"same", "individual", "random"}:
                level_mode = "individual"
            base_min = max(1, min(60, int(raw.get("base_level_min", 1))))
            base_max = max(1, min(60, int(raw.get("base_level_max", 60))))
            plus_min = max(0, min(90, int(raw.get("plus_level_min", 0))))
            plus_max = max(0, min(90, int(raw.get("plus_level_max", 90))))
        except (TypeError, ValueError, AttributeError):
            continue
        base_min, base_max = sorted((base_min, base_max))
        plus_min, plus_max = sorted((plus_min, plus_max))
        if cat_id in seen:
            continue
        seen.add(cat_id)
        out.append({
            "id": cat_id,
            "form": form,
            "base_level": base_level,
            "plus_level": plus_level,
            "level_mode": level_mode,
            "base_level_min": base_min,
            "base_level_max": base_max,
            "plus_level_min": plus_min,
            "plus_level_max": plus_max,
            "talent_action": (
                raw.get("talent_action")
                if raw.get("talent_action") in {"set", "disable_selected", "disable_all"}
                else "set"
            ),
            # 0は無効化。自然上限では丸めず、限界突破指定を保持する。
            "talents": {
                str(max(1, min(99999, int(talent_id)))): max(0, min(32767, int(level)))
                for talent_id, level in (raw.get("talents") or {}).items()
                if str(talent_id).lstrip("-").isdigit()
                and str(level).lstrip("-").isdigit()
            } if isinstance(raw.get("talents"), dict) else {},
        })
    return out


def safe_ototo_settings(data):
    """画面の表示レベルを、最新版で実在する城・部品・上限へ丸める。"""
    raw_settings = data.get("ototo_settings")
    if not isinstance(raw_settings, dict):
        return None
    try:
        cannons = get_ototo_metadata().get("cannons", [])
    except Exception:
        cannons = _bundled_ototo_metadata()["cannons"]
    definitions = {
        int(cannon["id"]): {
            int(part["id"]): (
                int(part.get("min_level", 0)),
                int(part.get("max_level", 0)),
            )
            for part in cannon.get("parts", [])
        }
        for cannon in cannons
    }
    output = {}
    for raw_cannon_id, raw_setting in list(raw_settings.items())[:64]:
        try:
            cannon_id = int(raw_cannon_id)
        except (TypeError, ValueError):
            continue
        if cannon_id not in definitions or not isinstance(raw_setting, dict):
            continue
        raw_levels = raw_setting.get("levels", {})
        if not isinstance(raw_levels, dict):
            continue
        levels = {}
        for raw_part_id, raw_level in list(raw_levels.items())[:3]:
            try:
                part_id = int(raw_part_id)
                minimum, maximum = definitions[cannon_id][part_id]
                level = max(minimum, min(maximum, int(raw_level)))
            except (TypeError, ValueError, KeyError):
                continue
            levels[str(part_id)] = level
        if levels:
            output[str(cannon_id)] = {"levels": levels}
    return output or None


# アカウント種別 → セーブファイル名のマッピング（ホワイトリスト方式。任意の文字列をパスに使わせない）
ACCOUNT_TYPE_FILES = {
    "new": "Nyanko_new",
    "beginner": "Nyanko_beginner",
    "intermediate": "Nyanko_Intermediate",
    "advanced": "Nyanko_advanced",
}


def safe_account_type(data):
    """account_type を検証済みのキーとして返す。不正・未指定なら 'new'（初期垢）。"""
    raw = str(data.get("account_type", "new")).strip()
    return raw if raw in ACCOUNT_TYPE_FILES else "new"


def safe_custom_amounts(data):
    out = {}
    for k in CUSTOM_KEYS:
        try:
            val = int(data.get(k, 0))
        except (TypeError, ValueError):
            val = 0
        # 極端な負値・過大値を丸める
        out[k] = max(0, min(val, 2_000_000_000))
    return out


# bcsfe 3.6.0 / JP 15.5.1。lengthは入力上限で、実際の有効数は
# 最新Gatyaitembuy metadataとセーブ配列長の両方で適用時に確認する。
VIP_ITEM_GROUPS = {
    "battle_items": {"length": 64, "max": 9999},
    "catseyes": {"length": 256, "max": 9999},
    "catamins": {"length": 256, "max": 9999},
    "base_materials": {"length": 256, "max": 9999},
    "catfruit": {"length": 512, "max": 998},
    "event_tickets": {"length": 512, "max": 9999},
    "labyrinth_medals": {"length": 4, "max": 32767},
}

VIP_ITEM_LABELS = {
    "battle_items": ["スピードアップ", "トレジャーレーダー", "ネコボン", "ニャンピュータ", "おかめはちもく", "スニャイパー"],
    "catseyes": ["キャッツアイ【EX】", "キャッツアイ【レア】", "キャッツアイ【激レア】", "キャッツアイ【超激レア】", "キャッツアイ【伝説】", "キャッツアイ【闇】"],
    "catamins": ["ネコビタンA", "ネコビタンB", "ネコビタンC"],
    "base_materials": [
        "レンガ", "羽根", "備長炭", "鋼の歯車", "黄金", "宇宙石", "謎の骨", "アンモナイト",
        "レンガZ", "羽根Z", "備長炭Z", "鋼の歯車Z", "黄金Z", "宇宙石Z", "謎の骨Z", "アンモナイトZ",
    ],
    "catfruit": [
        "紫マタタビの種", "赤マタタビの種", "青マタタビの種", "緑マタタビの種", "黄マタタビの種",
        "紫マタタビ", "赤マタタビ", "青マタタビ", "緑マタタビ", "黄マタタビ", "虹マタタビ",
        "古代マタタビの種", "古代マタタビ", "虹マタタビの種", "金マタタビ", "悪マタタビの種",
        "悪マタタビ", "金マタタビの種", "紫獣石", "紅獣石", "蒼獣石", "翠獣石", "黄獣石",
        "紫獣結晶", "紅獣結晶", "蒼獣結晶", "翠獣結晶", "黄獣結晶", "虹獣石",
    ],
    "labyrinth_medals": ["ブロンズ勲章", "シルバー勲章", "ゴールド勲章", "プラチナ勲章"],
}

VIP_ITEM_SELECTED_VALUES = {
    "battle_items": {"battle_items", "custom_battle_items"},
    "catseyes": {"catseyes", "custom_catseyes"},
    "catamins": {"catamins", "custom_catamins"},
    "base_materials": {"base_materials", "custom_base_materials"},
    "catfruit": {"matatabi", "custom_matatabi"},
    "event_tickets": {"event_tickets", "custom_event_tickets"},
    "labyrinth_medals": {"labyrinth_medals"},
}


def safe_vip_items(data):
    """VIP個別アイテムを {group: {index: amount}} に正規化する。"""
    raw_groups = data.get("vip_items", {})
    if not isinstance(raw_groups, dict):
        return {}
    result = {}
    try:
        dynamic_groups = get_legend_metadata().get("vip_item_groups", {})
    except Exception as e:
        print(f"[WARN] vip item metadata fallback: {e}")
        dynamic_groups = {}
    for group_key, spec in VIP_ITEM_GROUPS.items():
        raw_values = raw_groups.get(group_key, {})
        if not isinstance(raw_values, dict):
            continue
        values = {}
        for raw_index, raw_amount in raw_values.items():
            try:
                index = int(raw_index)
                amount = int(raw_amount)
            except (TypeError, ValueError):
                continue
            labels = dynamic_groups.get(group_key) or VIP_ITEM_LABELS.get(group_key, [])
            valid_length = min(spec["length"], len(labels)) if labels else spec["length"]
            if 0 <= index < valid_length:
                values[index] = max(0, min(amount, spec["max"]))
        # 空dictも保持する。これは「親項目は選択済みだが個別項目は全解除」を表す。
        if group_key in raw_groups:
            result[group_key] = values
    if "event_tickets" in raw_groups:
        raw_values = raw_groups.get("event_tickets", {})
        values = {}
        try:
            valid_ids = {item["id"] for item in get_legend_metadata().get("event_tickets", [])}
        except Exception as e:
            print(f"[ERROR] event ticket metadata: {e}")
            valid_ids = set()
        if isinstance(raw_values, dict):
            for ticket_id, raw_amount in raw_values.items():
                try:
                    amount = int(raw_amount)
                except (TypeError, ValueError):
                    continue
                if ticket_id in valid_ids:
                    values[ticket_id] = max(0, min(amount, 9999))
        result["event_tickets"] = values
    return result


def apply_vip_items(save, vip_items):
    """bcsfeの保存配列に、選択された種類だけを書き込む。"""
    logs = []
    dynamic_labels = {}
    if vip_items:
        try:
            dynamic_labels = get_legend_metadata().get("vip_item_groups", {})
        except Exception:
            dynamic_labels = {}
    targets = {
        "battle_items": getattr(getattr(save, "battle_items", None), "items", []),
        "catseyes": getattr(save, "catseyes", []),
        "catamins": getattr(save, "catamins", []),
        "base_materials": getattr(getattr(getattr(save, "ototo", None), "base_materials", None), "materials", []),
        "catfruit": getattr(save, "catfruit", []),
        "labyrinth_medals": getattr(save, "labyrinth_medals", []),
    }
    for group_key, values in (vip_items or {}).items():
        if group_key == "event_tickets":
            arrays = {
                1: getattr(save, "event_capsules", []),
                8: getattr(save, "lucky_tickets", []),
                10: getattr(save, "event_capsules_2", []),
            }
            for ticket_id, amount in values.items():
                try:
                    category, index = map(int, ticket_id.split(":"))
                    target = arrays.get(category, [])
                    if 0 <= index < len(target):
                        target[index] = amount
                        logs.append(f"イベントチケット[{ticket_id}]({amount})")
                except (TypeError, ValueError, IndexError) as e:
                    print(f"[ERROR] event ticket {ticket_id}: {e}")
            continue
        target = targets.get(group_key)
        labels = dynamic_labels.get(group_key) or VIP_ITEM_LABELS.get(group_key, [])
        if target is None:
            continue
        if group_key == "labyrinth_medals" and len(target) < 4:
            target.extend([0] * (4 - len(target)))
        for index, amount in values.items():
            if not 0 <= index < len(target):
                continue
            try:
                entry = target[index]
                if hasattr(entry, "amount"):
                    entry.amount = amount
                else:
                    target[index] = amount
                label = labels[index] if index < len(labels) else f"{group_key}[{index}]"
                logs.append(f"{label}({amount})")
            except Exception as e:
                print(f"[ERROR] vip_items {group_key}[{index}]: {e}")
    return logs


ERROR_CAT_IDS = [156, 183, 286, 321, 340, 354, 433, 434, 466, 493, 498, 499, 500, 501,
                 741, 742, 743, 744, 745, 746, 789, 674]


def update_web_data():
    global ERROR_CAT_IDS
    while True:
        try:
            r = requests.get(
                "https://battlecats-db.com/unit/r_all.html",
                headers={"User-Agent": "Mozilla/5.0"},
                timeout=30,
                proxies=PROXIES,
            )
            r.encoding = r.apparent_encoding
            if r.status_code == 200:
                soup = BeautifulSoup(r.text, "html.parser")
                no_list = []
                table = soup.find("table")
                if table:
                    for tr in table.find_all("tr"):
                        cells = tr.find_all("td")
                        if len(cells) >= 10:
                            no_text = cells[0].get_text(strip=True)
                            if no_text.isdigit():
                                no_list.append(int(no_text))
                if no_list:
                    ERROR_CAT_IDS = sorted(
                        list(set(range(1, max(no_list) + 1)) - set(no_list))
                        + [674]
                    )
        except Exception as e:
            print(f"[ERROR] update_web_data: {e}")
        time.sleep(60 * 60 * 24)


if os.getenv("DISABLE_BACKGROUND_UPDATER", "0") != "1":
    _updater_thread = threading.Thread(target=update_web_data, daemon=True)
    _updater_thread.start()


CUSTOM_KEYS = [
    "custom_catfood", "custom_xp", "custom_np",
    "custom_normal_tickets", "custom_rare_tickets",
    "custom_platinum_tickets", "custom_legend_tickets",
    "custom_leadership", "custom_battle_items", "custom_catamins",
    "custom_catseyes", "custom_base_materials", "custom_matatabi",
    "custom_talent_orbs", "custom_base_upgrades", "custom_event_tickets",
]


# メインステージの章ラベル（表示順=ポジション0〜8に対応。VIP限定の章選択機能で使用）
MAIN_STORY_CHAPTER_LABELS = [
    "日本編1章", "日本編2章", "日本編3章",
    "未来編1章", "未来編2章", "未来編3章",
    "宇宙編1章", "宇宙編2章", "宇宙編3章",
]

# 表示上のポジション(0〜8) → save.story.chapters の実インデックスへの変換テーブル。
# ゾンビ編と同様に実データ上ではインデックス3が欠番のため、日本編0,1,2 → 未来編4,5,6 → 宇宙編7,8,9 とスキップする。
MAIN_STORY_REAL_INDEX = [0, 1, 2, 4, 5, 6, 7, 8, 9]


# レジェンド系の表示名はbcsfeのゲームデータから取得する。セーブ配列の種類と
# Map_Name / StageName のコードを同じ表で管理し、画面と適用処理のずれを防ぐ。
LEGEND_SERIES = {
    "legend": {"label": "レジェンドストーリー", "code": "N", "base_index": 0},
    "true_legend": {"label": "真レジェンドストーリー", "code": "NA", "base_index": 13000},
    "zero_legend": {"label": "零レジェンドストーリー", "code": "ND", "base_index": 34000},
}
LEGEND_SELECTED_VALUES = {
    "legend": "legend_clear",
    "true_legend": "true_legend_clear",
    "zero_legend": "zero_legend_clear",
}
EVENT_STAGE_FAMILIES = {
    "event": {"label": "イベントステージ", "code": "S", "base_index": 1000, "kind": "event", "group": 1},
    "collab": {"label": "コラボステージ", "code": "C", "base_index": 2000, "kind": "event", "group": 2},
    "dojo_ranking": {"label": "ランキングの間", "code": "R", "base_index": 6000, "kind": "event", "group": 3},
    "tower": {"label": "にゃんこ塔・異界にゃんこ塔", "code": "V", "base_index": 7000, "kind": "tower"},
    "catamin": {"label": "ネコビタンステージ", "code": "B", "base_index": 14000, "kind": "catamin_stages"},
    "legend_quest": {"label": "レジェンドクエスト", "code": "D", "base_index": 16000, "kind": "legend_quest"},
    "gauntlets": {"label": "強襲ステージ（各月・夏休み系を含む）", "code": "A", "base_index": 24000, "kind": "gauntlets"},
    "enigma": {"label": "発掘・地図ステージ", "code": "H", "base_index": 25000, "kind": "enigma_clears"},
    "collab_gauntlets": {"label": "コラボ強襲", "code": "CA", "base_index": 27000, "kind": "collab_gauntlets"},
    "behemoth": {"label": "超獣討伐ステージ", "code": "Q", "base_index": 31000, "kind": "behemoth_culling"},
    "labyrinth": {
        "label": "地底迷宮",
        "code": "L",
        "base_index": 33000,
        "kind": "labyrinth",
        "stage_file": "StageName_L_ja.csv",
        "uses_clear_count": False,
    },
    "colosseum": {"label": "異次元コロシアム", "code": "SR", "base_index": 36000, "kind": "event", "group": 4},
    "catclaw": {"label": "にゃんこ道検定", "code": "G", "base_index": 37000, "kind": "dojo_chapters", "stage_file": "StageName_G_ja.csv"},
}
MAX_STAGE_CLEAR_COUNT = 32767
MAX_DETAILED_STAGE_SELECTIONS = 50000
MAX_LABYRINTH_CHARACTERS = 10000
LABYRINTH_CHARACTER_ACTIONS = {
    "unlock_selected", "unlock_all", "seal_selected", "seal_all",
    "release_lineup_all",
}
_legend_metadata_cache = None
_legend_metadata_cached_at = 0.0
_legend_metadata_lock = threading.Lock()
LEGEND_METADATA_TTL = 15 * 60
_character_metadata_cache = None
_character_metadata_cached_at = 0.0
_character_metadata_lock = threading.Lock()
CHARACTER_METADATA_TTL = 15 * 60
_ototo_metadata_cache = None
_ototo_metadata_cached_at = 0.0
_ototo_metadata_lock = threading.Lock()
OTOTO_METADATA_TTL = 15 * 60

# GatyaData_Option_SetR.tsv の seriesID に対応する表示名。未登録の新規系列は
# ID付きの名称で表示し、データ更新で画面全体が使えなくならないようにする。
GACHA_SERIES_NAMES = {
    0: "伝説のネコルガ族", 1: "超激ダイナマイツ", 2: "戦国武神バサラーズ",
    3: "電脳学園ギャラクシーギャルズ", 4: "超破壊大帝ドラゴンエンペラーズ",
    5: "レッドバスターズ", 6: "超古代勇者ウルトラソウルズ",
    7: "逆襲の英雄ダークヒーローズ", 8: "ハロウィンガチャ",
    9: "クリスマスギャルズ", 11: "「ゆるドラシル」コラボガチャ",
    13: "「メルクストーリア」コラボガチャ", 14: "「生きろ！マンボウ！」コラボガチャ",
    15: "「消滅都市」コラボガチャ", 16: "新年ガチャ",
    17: "「ケリ姫スイーツ」コラボガチャ", 18: "究極降臨ギガントゼウス",
    19: "超ネコ祭", 21: "プラチナガチャ", 22: "エアバスターズ",
    23: "「魔法少女まどか☆マギカ」コラボガチャ",
    24: "革命軍隊アイアンウォーズ", 26: "イースターカーニバル",
    27: "極ネコ祭", 28: "絶命美少女ギャルズモンスターズ",
    32: "メタルバスターズ", 33: "大精霊エレメンタルピクシーズ",
    34: "劇場版「Fate/stay night [Heaven's Feel]」コラボガチャ",
    35: "超選抜祭", 37: "「エヴァンゲリオン」コラボガチャ",
    38: "「ビックリマン」コラボガチャ", 39: "極選抜祭", 42: "超極ネコ祭",
    43: "「初音ミク」コラボガチャ", 44: "「エヴァンゲリオン」コラボガチャ 2nd",
    45: "波動バスターズ", 46: "レジェンドガチャ", 47: "超国王祭",
    48: "バレンタインギャルズ", 49: "「らんま1/2」コラボガチャ",
    50: "女王祭", 52: "ホワイトデーガチャ", 53: "ジューンブライドガチャ",
    54: "「ストリートファイター6」コラボガチャ BLUE TEAM",
    55: "「ストリートファイター6」コラボガチャ RED TEAM",
    56: "超生命体バスターズ", 57: "熱血！大運動会 赤組",
    58: "熱血！大運動会 白組", 59: "バスターズ祭",
    60: "「メタルスラッグアタック」コラボガチャ",
    63: "「るろうに剣心 -明治剣客浪漫譚-」コラボガチャ",
    64: "サマーガールズ サンシャイン", 65: "サマーガールズ ブルーオーシャン",
    66: "ウルトラ4セレクション", 67: "ミラクル4セレクション",
    68: "エクセレント4セレクション", 69: "1億DL記念ガチャ",
    70: "DL記念選抜ガチャ", 71: "アウトレットガチャ",
    72: "「範馬刃牙」コラボガチャ", 73: "「ソニック・ザ・ヘッジホッグ」コラボガチャ",
    74: "アニメ「鬼滅の刃」コラボガチャ", 75: "熱血！大運動会 黒組",
}

# JP 15.6.0 の有効なガチャ系列と所属キャラID。最新版取得に失敗した時も
# コラボ・ガチャ絞り込みを継続できるよう、gzip+base64で同梱する。
BUNDLED_CHARACTER_GROUPS_B64 = (
    "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"
)
BUNDLED_CHARACTER_RARITIES_B64 = (
    "H4sIAGTjcmoC/41UW24EMQi7UD/W4Jxm1ftfo22GgGFmpQpNdpXwMhjer68p+Ld4CPdpv3L9cgv2Tcm5YXyeGhyWFucRxH29+U0scvoU3SLTSwfhC5GHjygHIQNXeTh5Hn0X7YrO7ZNxc060KL4jI2+qfmg+jw5GJtaq4g21Z41Ko3K0h9p2HN7yZNSh7BkaLjn48GvZLQ5UHvVgZqBeTaJSusnoFm//GN6eBZLTsTvecKuqD0skT/BBa3INYeNS956hCW9XyKW30tvfC/Zn+5atkgjt82qtUxc7VuIsbhbzLaJxzJbv2CYzSLGjTOaFazUeVkc9cbvMLG598rYhLlmJxts9G77DnGIHm38TbhTrajoh/H8lo3X6XVhauUKmhdnluak80SN77y2nQt1RQmJRtgNlglbUCFGvJdPUN4wJqjkXaG/etKxNXrd22Uqfas5gxxJvMze2/fYknhNY20e10ZDg+wcx0WfLzwYAAA=="
)
# JP 15.5.0 nyankoPictureBookData.csvの実装形態数。Unit_Explanationには
# 未実装形態用として直前の名前を複製した行があるため、名前の行数では判定しない。
# ID456（モモコ）だけは提供された15.5.1実機の進化前後セーブ差分で第3形態を確認済み。
BUNDLED_CHARACTER_FORM_COUNTS_B64 = (
    "H4sIAOdwfGoC/51T2w0DIQxbqD9x2Kbq/mtUpT0gsQOnKkLikdjOg6c//jF0O/lwzLVvw4NxWl+tRKqY4z0W/GknrZP75P+xFk4q4uuFRR8GG2T+rHsqwzab+vVOt5w4kaqTkVEyr/Ft9JK7A4mjum6hw0i+IDbWkpUxFs9hjHc6z/7m7NuYEK4IivlTWuOEcMWjsqgyKgFhqUgXNUXJq+qbK6xnD6W53PnW26kv6i/lieafAjFbLqu/5mHy97jQpqcOqbKZMffM+s5+67rD1mxhtAUlRxtF4QayFffx3Y6odiuPGsVfb+qOjK3PBgAA"
)
# unitbuy.csvのforce_true_form_levelから生成した、自然な第三形態取得状態。
# 0=レベル到達で自動進化、2=素材/報酬等で取得。JP 15.5.0・871体。
BUNDLED_CHARACTER_TRUE_FORM_STATES_B64 = (
    "H4sIAJh1fGoC/4s20EGHRqNwFI7CUTiC4GipNyxgLAD9s0vDzwYAAA=="
)
BUNDLED_TALENT_DATA_B64 = "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"
BUNDLED_CHARACTER_DATA_B64 = (
    "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"
    "TLAzHjQZ0TQTEYLP1cM3aJBRhyMoOGJVd7KgvW8QwD/sJEaIwr9LRoCzE/uK5DluDhGEDUYTXbzowaczWYBTBq+1URpiwXePxlae"
    "5+/iCYeO+sDKUHj26AHBpktHWOE5t7wUHG3CwQmTbV1ir60uJAWCRj3aEHxK0SXf2muOC3NdoDe1W3pLAnDFDrJay+2Jgllf//nf"
    "/7ffNs8Xk0BoadJrXHx+Uu97PJhZ1WcZC4l0/TYBeLuJCF60q5n/sen7lPRkcuAUpTmqY9gzWTe+7iNOXJK7ir+Mt9ioAZhCI4Zm"
    "8edOokFCKN5bHqriqcp6i/rHEXMrJuYIBE07/agnsSRGIK4ZMRJ71BhwbYiZXgx6Sp6jJ+YG+7kd6+GJ6yj8u2QEeLJfykMu3Bpk"
    "nidsHKvCDqITqlkIu+adY1J9l4oD524J7FfdJibaE0c/aOh0/Ig3ptfVqBJmJuz7VDsclCMeQhHsb96DRh9ZBNcHe9P8BVIViA5N"
    "uiYRKDQnAXZDK1W8TYwdABSzxuiVe6qnbf8ZgpMFBsV16rZQScCCGaSzEp9/MC/lOkHznIYCp36Xk1m73HYG2IJ3Kg3So3XAvceJ"
    "h9XPzYLv+1BgyeZ7uD6nvAeNTX0bCQTgndF+xQfGKUWrtjbl77uw4GrtPc3ll/B6J5a37EkLs06YcHGDyW60xs84i2fY1l+fKDd3"
    "z8mjH84T/BdZKOPwfw2EgrJTiEX8+DfC0h5y6qMP4YDNsUAu+j5ErwEP+myjH4vmlvrLLgr0b0b+7RI8ZztYLChBOzzeVPK1CWry"
    "gbCnPfJ08gga1XUioDVlT6vWT3QwYabPbj71mUIwNOPsOSVPAS+/4kb8OWFgBA+aE82Hl/rqGZ+Ij7WHqly763hyfgXTCrn8aPiH"
    "H3NK0qrlKsgdyfzk2uUX5ksk1BgyMOiEnBYePZBsmjcus3LtPVAcCB68pdzd8Avd1IrrTa9pBIJ2NGxfn2aCgdFwfRpiBi68x45A"
    "0NQk1N2v5fdrOfXwRT2xLcR/myko8HPP4Pa7eJbld2HB1ckr6XydpHbtYcHVyezkfLKkdu1hwbXPS/jG3zGh0ZsoMLPSlfmy8RZv"
    "o5B10rE1enOGIL7tP4ptYwp1dTjWR28KxdlHsUkzqqvDTe0XH6Bagm8fBa4Jef702v3gp1TVWFl54DS4lZT271ZnAJvRa2xXh3WI"
    "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"
    "mhrgsDjTHJk1L/Vv/vf/Ayvdy29ODAEA"
)
FACILITY_NAMES = [
    "にゃんこ砲攻撃力", "にゃんこ砲射程", "にゃんこ砲チャージ",
    "働きネコ仕事効率", "働きネコお財布", "お城体力",
    "研究力", "会計力", "勉強力", "統率力",
]


def _clean_stage_names(values):
    names = []
    for value in values or []:
        name = str(value).strip()
        if not name or name == "＠":
            break
        names.append(name)
    return names


def _latest_jp_game_data_getter():
    """BCSFEの配布一覧を数値版で比較し、JPの実在する最新版を返す。"""
    cc = core.CountryCode.from_code("jp")
    parsed_versions = list(core.GameDataGetter.get_downloaded_versions_region(cc))
    try:
        repo_metadata = core.GameDataGetter.get_metadata(show_alt=False) or {}
        versions = list(core.GameDataGetter.get_versions(repo_metadata).get(cc.get_code(), {}))
    except Exception as e:
        print(f"[WARN] game data version list: {e}")
        versions = []
    for version in versions:
        try:
            parsed_versions.append(core.GameVersion.from_string(version))
        except (TypeError, ValueError):
            continue
    if parsed_versions:
        latest = max(parsed_versions, key=lambda version: version.game_version)
        return core.GameDataGetter(cc, latest, do_print=False)
    # ネットワークもローカルデータもない時に、BCSFEのCLI用確認プロンプトを
    # Webワーカー上で開かないための空getter。各機能はNoneを受けて安全に失敗する。
    getter = object.__new__(core.GameDataGetter)
    getter.print = False
    getter.lang = core.core_data.config.get_str(core.ConfigKey.LOCALE)
    getter.real_cc = cc
    getter.cc = cc.get_cc_lang()
    getter.gv = core.GameVersion(TARGET_GAME_VERSION_NUMBER)
    getter.version = None
    getter.all_versions = None
    getter.url = None
    getter.filepath = None
    return getter


def _character_groups_from_series(series_members):
    """seriesIDごとのキャラ集合を画面用の安定した一覧へ変換する。"""
    groups = []
    for raw_series_id, raw_cat_ids in series_members.items():
        try:
            series_id = int(raw_series_id)
        except (TypeError, ValueError):
            continue
        cat_ids = sorted({
            max(1, min(9999, int(cat_id)))
            for cat_id in raw_cat_ids
            if str(cat_id).lstrip("-").isdigit() and 1 <= int(cat_id) <= 9999
        })
        if not cat_ids:
            continue
        name = GACHA_SERIES_NAMES.get(series_id, f"ガチャシリーズ #{series_id}")
        groups.append({
            "id": f"series_{series_id}",
            "series_id": series_id,
            "name": name,
            "kind": "collab" if "コラボ" in name else "gacha",
            "cat_ids": cat_ids,
        })
    return sorted(groups, key=lambda item: (item["kind"] != "collab", item["series_id"]))


def _bundled_character_groups():
    try:
        payload = json.loads(gzip.decompress(base64.b64decode(BUNDLED_CHARACTER_GROUPS_B64)))
    except (ValueError, OSError, gzip.BadGzipFile):
        return []
    return _character_groups_from_series(payload if isinstance(payload, dict) else {})


def _download_character_groups(getter):
    """最新版の有効ガチャから、コラボ・ガチャ系列ごとの所属キャラを作る。"""
    set_data = getter.download("DataLocal", "GatyaDataSetR1.csv")
    option_data = getter.download("DataLocal", "GatyaData_Option_SetR.tsv")
    if set_data is None or option_data is None:
        return _bundled_character_groups()

    sets = []
    for row in core.CSV(set_data, remove_empty=False).lines:
        members = []
        for field in row:
            cat_id = field.to_int()
            if cat_id < 0:
                break
            members.append(cat_id + 1)  # ゲームデータは0始まり、画面は1始まり。
        sets.append(members)

    series_members = {}
    lines = option_data.to_str().replace("\r\n", "\n").split("\n")
    for line in lines[1:]:
        columns = line.split("\t")
        if len(columns) < 6:
            continue
        try:
            set_id = int(columns[0])
            banner_enabled = int(columns[1])
            series_id = int(columns[5])
        except ValueError:
            continue
        if banner_enabled != 1 or not (0 <= set_id < len(sets)):
            continue
        series_members.setdefault(series_id, set()).update(sets[set_id])
    groups = _character_groups_from_series(series_members)
    return groups or _bundled_character_groups()


def _bundled_character_metadata():
    """通信失敗時に使う、同梱済みJPキャラ情報。"""
    try:
        payload = json.loads(gzip.decompress(base64.b64decode(BUNDLED_CHARACTER_DATA_B64)))
        rarities = json.loads(gzip.decompress(base64.b64decode(BUNDLED_CHARACTER_RARITIES_B64)))
        form_counts = json.loads(gzip.decompress(base64.b64decode(BUNDLED_CHARACTER_FORM_COUNTS_B64)))
        true_form_states = json.loads(gzip.decompress(base64.b64decode(BUNDLED_CHARACTER_TRUE_FORM_STATES_B64)))
        bundled_talents = json.loads(gzip.decompress(base64.b64decode(BUNDLED_TALENT_DATA_B64)))
    except (ValueError, OSError, gzip.BadGzipFile) as e:
        raise RuntimeError("内蔵キャラ名データを読み込めません") from e

    rarity_names = ["基本キャラ", "EX", "レア", "激レア", "超激レア", "伝説レア"]
    characters = []
    for display_id, raw_names in payload.get("characters", []):
        display_id = int(display_id)
        names = [str(name).strip() for name in raw_names if str(name).strip()]
        if not names:
            continue
        rarity = rarities[display_id - 1] if display_id - 1 < len(rarities) else -1
        form_count = form_counts[display_id - 1] if display_id - 1 < len(form_counts) else 1
        # ユーザー提供のJP 15.5.1実機セーブで実装を確認した公開データ差分。
        # 自然な第三形態取得状態はunitbuy由来の0/2を別metadataで保持する。
        if display_id == 456:
            form_count = max(form_count, 3)
        form_count = max(1, min(4, int(form_count)))
        names = names[:form_count]
        while len(names) < form_count:
            names.append(names[-1] if names else f"No.{display_id} 第{len(names) + 1}形態")
        selectable = display_id not in ERROR_CAT_IDS and not all(
            re.fullmatch(r"\d+[-_]\d+", name) for name in names
        )
        characters.append({
            "id": display_id,
            "names": names,
            "form_count": form_count,
            "selectable": selectable,
            "true_form_state": (
                int(true_form_states[display_id - 1])
                if display_id - 1 < len(true_form_states) else 2
            ),
            "rarity": rarity,
            "rarity_name": rarity_names[rarity] if 0 <= rarity < len(rarity_names) else "不明",
            "talents": bundled_talents.get(str(display_id), []),
        })
    return {
        "data_version": str(payload.get("version", "bundled-jp")),
        "source": "bundled",
        "rarity_names": rarity_names,
        "characters": characters,
        "groups": _bundled_character_groups(),
    }


def _download_character_metadata():
    """最新BCSFE JPデータから名前・レアリティ・実装形態数を組み立てる。"""
    cc = core.CountryCode.from_code("jp")
    getter = _latest_jp_game_data_getter()
    picture_data = getter.download("DataLocal", "nyankoPictureBookData.csv")
    unit_buy_data = getter.download("DataLocal", "unitbuy.csv")
    skill_data = getter.download("DataLocal", "SkillAcquisition.csv")
    skill_name_data = getter.download("resLocal", "SkillDescriptions.csv")
    if picture_data is None or unit_buy_data is None:
        raise RuntimeError("最新JPキャラ定義を取得できません")

    picture_rows = core.CSV(picture_data).lines
    unit_buy_rows = core.CSV(unit_buy_data).lines
    talent_names = {}
    if skill_name_data is not None:
        for row in core.CSV(
            skill_name_data,
            core.Delimeter.from_country_code_res(cc),
            remove_empty=False,
        ).lines[1:]:
            if len(row) >= 2:
                talent_names[row[0].to_int()] = row[1].to_str().split("<br>", 1)[0].strip()
    talents_by_cat = {}
    if skill_data is not None:
        for row in core.CSV(skill_data, remove_empty=False).lines[1:]:
            if len(row) < 16:
                continue
            cat_id = row[0].to_int()
            talents = []
            for slot, offset in enumerate(range(2, len(row) - 13, 14)):
                ability_id = row[offset].to_int()
                max_level = row[offset + 1].to_int() or 1
                text_id = row[offset + 10].to_int()
                is_ultra = bool(row[offset + 13].to_int())
                if ability_id <= 0 or text_id <= 0:
                    continue
                talents.append({
                    "id": ability_id,
                    "name": talent_names.get(text_id) or f"本能 {ability_id}",
                    "max_level": max(1, max_level),
                    "category": "超本能" if is_ultra else "本能",
                    "ultra": is_ultra,
                    "slot": slot,
                })
            if talents:
                talents_by_cat[cat_id] = talents
    rarity_names = ["基本キャラ", "EX", "レア", "激レア", "超激レア", "伝説レア"]
    characters = []
    for cat_id, picture_row in enumerate(picture_rows):
        if len(picture_row) < 3:
            continue
        form_count = max(1, min(4, picture_row[2].to_int()))
        rarity = unit_buy_rows[cat_id][13].to_int() if cat_id < len(unit_buy_rows) and len(unit_buy_rows[cat_id]) > 13 else -1
        name_data = getter.download("resLocal", f"Unit_Explanation{cat_id + 1}_ja.csv")
        names = []
        if name_data is not None:
            name_rows = core.CSV(
                name_data,
                core.Delimeter.from_country_code_res(cc),
                remove_empty=False,
            ).lines
            names = [row[0].to_str().strip() for row in name_rows if len(row)]
        # 15.5.1実機の進化前後セーブ差分で、モモコ(ID456)の第3形態を確認済み。
        # Unit_Explanationの未実装用重複行を一般化すると大量の誤表示になるため、
        # 公開picture bookとの差分補正は実測できたキャラだけに限定する。
        if cat_id + 1 == 456:
            form_count = max(form_count, 3)
        names = [name for name in names[:form_count] if name]
        while len(names) < form_count:
            names.append(names[-1] if names else f"No.{cat_id + 1} 第{len(names) + 1}形態")
        selectable = cat_id + 1 not in ERROR_CAT_IDS and not all(
            re.fullmatch(r"\d+[-_]\d+", name) for name in names
        )
        characters.append({
            "id": cat_id + 1,
            "names": names,
            "form_count": form_count,
            "selectable": selectable,
            "true_form_state": (
                0 if cat_id < len(unit_buy_rows)
                and len(unit_buy_rows[cat_id]) > 20
                and unit_buy_rows[cat_id][20].to_int() >= 0
                else 2
            ),
            "rarity": rarity,
            "rarity_name": rarity_names[rarity] if 0 <= rarity < len(rarity_names) else "不明",
            "talents": talents_by_cat.get(cat_id, []),
        })

    if not characters:
        raise RuntimeError("最新JPキャラ名データが空です")
    return {
        "data_version": getter.version or "latest-jp",
        "source": "bcsfe",
        "rarity_names": rarity_names,
        "characters": characters,
        "groups": _download_character_groups(getter),
    }


def get_character_metadata():
    """BCSFEの最新JPキャラ情報を返し、通信失敗時だけ同梱版へ切り替える。"""
    global _character_metadata_cache, _character_metadata_cached_at
    if _character_metadata_cache is not None and time.time() - _character_metadata_cached_at < CHARACTER_METADATA_TTL:
        return _character_metadata_cache
    with _character_metadata_lock:
        if _character_metadata_cache is not None and time.time() - _character_metadata_cached_at < CHARACTER_METADATA_TTL:
            return _character_metadata_cache
        try:
            metadata = _download_character_metadata()
        except Exception as e:
            print(f"[WARN] latest character metadata fallback: {e}")
            metadata = _bundled_character_metadata()
        if not metadata.get("characters"):
            raise RuntimeError("キャラ名データを取得できません")
        _character_metadata_cache = metadata
        _character_metadata_cached_at = time.time()
        return _character_metadata_cache


def _bundled_ototo_metadata():
    names = [
        "にゃんこ城強化", "スロウ砲", "鉄壁砲", "かみなり砲",
        "水鉄砲", "エンジェル砲", "キャノンブレイク砲", "呪い砲",
    ]
    output = []
    for cannon_id, name in enumerate(names):
        if cannon_id == 0:
            parts = [{"id": 0, "name": "城体力", "min_level": 1, "max_level": 30}]
        else:
            parts = [
                {"id": 0, "name": "主砲", "min_level": 1, "max_level": 30},
                {"id": 1, "name": "土台", "min_level": 0, "max_level": 20},
                {"id": 2, "name": "装飾", "min_level": 0, "max_level": 20},
            ]
        output.append({"id": cannon_id, "name": name, "parts": parts})
    return {"data_version": "bundled-jp-15.6.0", "source": "bundled", "cannons": output}


def _download_ototo_metadata():
    cc = core.CountryCode.from_code("jp")
    getter = _latest_jp_game_data_getter()
    description_data = getter.download("resLocal", "CastleRecipeDescriptions.csv")
    unlock_data = getter.download("DataLocal", "CastleRecipeUnlock.csv")
    if description_data is None or unlock_data is None:
        raise RuntimeError("オトート定義を取得できません")

    max_levels = {}
    for row in core.CSV(unlock_data, remove_empty=False).lines:
        if len(row) < 5:
            continue
        cannon_id, part_id, level = row[0].to_int(), row[1].to_int(), row[4].to_int()
        if cannon_id < 0 or part_id not in {0, 1, 2} or level < 0:
            continue
        max_levels[(cannon_id, part_id)] = max(max_levels.get((cannon_id, part_id), 0), level)

    cannons = []
    rows = core.CSV(
        description_data,
        delimiter=core.Delimeter.from_country_code_res(cc),
        remove_empty=False,
    ).lines
    for row in rows:
        if len(row) < 9:
            continue
        cannon_id = row[0].to_int()
        if cannon_id < 0:
            continue
        name = row[1].to_str().strip() or row[6].to_str().strip() or f"城強化 #{cannon_id}"
        part_ids = [part_id for part_id in (0, 1, 2) if (cannon_id, part_id) in max_levels]
        if not part_ids:
            continue
        part_names = {
            0: "城体力" if cannon_id == 0 else "主砲",
            1: row[7].to_str().strip() or "土台",
            2: row[8].to_str().strip() or "装飾",
        }
        parts = [{
            "id": part_id,
            "name": part_names[part_id],
            "min_level": 1 if part_id == 0 else 0,
            "max_level": max_levels[(cannon_id, part_id)],
        } for part_id in part_ids]
        cannons.append({"id": cannon_id, "name": name, "parts": parts})
    if not cannons:
        raise RuntimeError("オトート定義が空です")
    return {
        "data_version": getter.version or "latest-jp",
        "source": "bcsfe",
        "cannons": cannons,
    }


def get_ototo_metadata():
    global _ototo_metadata_cache, _ototo_metadata_cached_at
    if _ototo_metadata_cache is not None and time.time() - _ototo_metadata_cached_at < OTOTO_METADATA_TTL:
        return _ototo_metadata_cache
    with _ototo_metadata_lock:
        if _ototo_metadata_cache is not None and time.time() - _ototo_metadata_cached_at < OTOTO_METADATA_TTL:
            return _ototo_metadata_cache
        try:
            metadata = _download_ototo_metadata()
        except Exception as e:
            print(f"[WARN] latest ototo metadata fallback: {e}")
            metadata = _bundled_ototo_metadata()
        _ototo_metadata_cache = metadata
        _ototo_metadata_cached_at = time.time()
        return _ototo_metadata_cache


def get_legend_metadata():
    """bcsfeの最新JPゲームデータから章名・ステージ名・実装済み冠数を返す。"""
    global _legend_metadata_cache, _legend_metadata_cached_at
    if _legend_metadata_cache is not None and time.time() - _legend_metadata_cached_at < LEGEND_METADATA_TTL:
        return _legend_metadata_cache
    with _legend_metadata_lock:
        if _legend_metadata_cache is not None and time.time() - _legend_metadata_cached_at < LEGEND_METADATA_TTL:
            return _legend_metadata_cache

        cc = core.CountryCode.from_code("jp")
        # 文字列順では15.10と15.9を誤判定し得るため、配布版を数値比較する。
        getter = _latest_jp_game_data_getter()
        map_name_data = getter.download("resLocal", "Map_Name.csv")
        map_option_data = getter.download("DataLocal", "Map_option.csv")
        if map_name_data is None or map_option_data is None:
            raise RuntimeError("最新JPゲームデータを取得できません")
        map_name_csv = core.CSV(map_name_data, core.Delimeter.from_country_code_res(cc))
        all_map_names = {
            row[0].to_int(): row[1].to_str().strip()
            for row in map_name_csv if len(row) >= 2
        }
        map_option = core.MapOption.from_csv(core.CSV(map_option_data))
        # 異次元コロシアムは全章のMap_Nameが同名なので、特殊ルール名を章名へ足す。
        special_rule_names = {}
        special_rules_data = getter.download("DataLocal", "SpecialRulesMap.json")
        localizable_data = getter.download("resLocal", "localizable.tsv")
        if special_rules_data is not None and localizable_data is not None:
            localizable_names = {
                row[0].to_str().strip(): row[1].to_str().strip()
                for row in core.CSV(localizable_data, "\t") if len(row) >= 2
            }
            raw_rule_maps = core.JsonFile.from_data(special_rules_data).as_object().get("MapID", {})
            for raw_map_id, rule in raw_rule_maps.items():
                try:
                    full_map_id = int(raw_map_id)
                except (TypeError, ValueError):
                    continue
                label = str(rule.get("RuleNameLabel", "")) if isinstance(rule, dict) else ""
                if label and localizable_names.get(label):
                    special_rule_names[full_map_id] = localizable_names[label]
        metadata = {}
        for series_key, spec in LEGEND_SERIES.items():
            stage_data = getter.download(
                "resLocal", f"StageName_R{spec['code']}_ja.csv"
            )
            if stage_data is None:
                raise RuntimeError(f"{series_key}のステージ名を取得できません")
            stage_csv = core.CSV(stage_data, core.Delimeter.from_country_code_res(cc))
            maps = []
            for map_id, row in enumerate(stage_csv):
                stage_names = _clean_stage_names(row.to_str_list())
                map_name = all_map_names.get(spec["base_index"] + map_id)
                if not stage_names or not map_name:
                    continue
                option = map_option.get_map(spec["base_index"] + map_id) if map_option else None
                crown_count = max(1, min(4, int(option.crown_count if option else 4)))
                maps.append({
                    "id": map_id,
                    "name": map_name,
                    "stages": stage_names,
                    "crowns": crown_count,
                })
            metadata[series_key] = {"label": spec["label"], "maps": maps}

        # ゾンビ襲来はメイン3編×各3章。セーブ内のステージ順に並べ替えて返す。
        story_stage_names = {}
        for chapter_type in range(3):
            stage_data = getter.download("resLocal", f"StageName{chapter_type}_ja.csv")
            if stage_data is None:
                raise RuntimeError(f"ゾンビ編{chapter_type}のステージ名を取得できません")
            stage_csv = core.CSV(stage_data, core.Delimeter.from_country_code_res(cc))
            source_names = [row[0].to_str().strip() for row in stage_csv if len(row)]
            story_stage_names[chapter_type] = [
                source_names[stage_id if stage_id >= 46 else 45 - stage_id]
                for stage_id in range(min(48, len(source_names)))
            ]
        metadata["zombie"] = {
            "label": "ゾンビ襲来",
            "chapters": [
                {
                    "id": position,
                    "real_id": MAIN_STORY_REAL_INDEX[position],
                    "name": MAIN_STORY_CHAPTER_LABELS[position],
                    "stages": story_stage_names[position // 3],
                }
                for position in range(len(MAIN_STORY_CHAPTER_LABELS))
            ],
        }
        metadata["main_story"] = {
            "label": "メインステージ",
            "chapters": [
                {
                    "id": position,
                    "real_id": MAIN_STORY_REAL_INDEX[position],
                    "name": MAIN_STORY_CHAPTER_LABELS[position],
                    "stages": story_stage_names[position // 3],
                }
                for position in range(len(MAIN_STORY_CHAPTER_LABELS))
            ],
        }

        # bcsfeの各ステージ編集機能と同じ文字コード・ベースIDを使う。
        # 通常イベントだけでなく、塔・強襲・超獣・地図・コラボもまとめて返す。
        event_families = {}
        for family_key, family_spec in EVENT_STAGE_FAMILIES.items():
            stage_file = family_spec.get(
                "stage_file", f"StageName_R{family_spec['code']}_ja.csv"
            )
            stage_data = getter.download(
                "resLocal", stage_file
            )
            if stage_data is None:
                continue
            stage_csv = core.CSV(stage_data, core.Delimeter.from_country_code_res(cc))
            maps = []
            for map_id, row in enumerate(stage_csv):
                stage_names = _clean_stage_names(row.to_str_list())
                full_map_id = family_spec["base_index"] + map_id
                map_name = all_map_names.get(full_map_id)
                if not stage_names or not map_name:
                    continue
                if family_key == "colosseum" and special_rule_names.get(full_map_id):
                    map_name = f"{map_name}【{special_rule_names[full_map_id]}】"
                option = map_option.get_map(full_map_id) if map_option else None
                crown_count = max(1, min(4, int(option.crown_count if option else 1)))
                maps.append({
                    "id": map_id,
                    "name": map_name,
                    "stages": stage_names,
                    "crowns": crown_count,
                })
            event_families[family_key] = {
                "label": family_spec["label"],
                "maps": maps,
                "uses_clear_count": family_spec.get("uses_clear_count", True),
            }
        metadata["event_stage_families"] = event_families

        aku_stage_data = getter.download("resLocal", "StageName_DM_ja.csv")
        if aku_stage_data is None:
            raise RuntimeError("魔界編のステージ名を取得できません")
        aku_stage_csv = core.CSV(aku_stage_data, core.Delimeter.from_country_code_res(cc))
        aku_stage_names = _clean_stage_names([
            value.to_str() for row in aku_stage_csv for value in row
        ])
        metadata["aku"] = {
            "label": "魔界編",
            "chapters": [{"id": 0, "name": "魔界編", "stages": aku_stage_names}],
        }
        aku_ex_stage_data = getter.download("resLocal", "StageName_RE_ja.csv")
        if aku_ex_stage_data is None:
            raise RuntimeError("魔界編EXのステージ名を取得できません")
        aku_ex_stage_csv = core.CSV(aku_ex_stage_data, core.Delimeter.from_country_code_res(cc))
        aku_ex_names = _clean_stage_names(aku_ex_stage_csv[42].to_str_list())
        metadata["aku_ex"] = {
            "label": "魔界編EX",
            "chapters": [{
                "id": 0,
                "name": all_map_names.get(4042, "富士山EX"),
                "stages": aku_ex_names or ["富士山"],
            }],
        }

        metadata["data_version"] = getter.version

        ability_data = getter.download("DataLocal", "AbilityData.csv")
        if ability_data is None:
            raise RuntimeError("施設データを取得できません")
        ability_csv = core.CSV(ability_data)
        metadata["facilities"] = [
            {
                "id": facility_id,
                "name": FACILITY_NAMES[facility_id],
                "max_base": ability_csv[facility_id][2].to_int(),
                "max_plus": ability_csv[facility_id][3].to_int(),
                "max_level": ability_csv[facility_id][2].to_int() + ability_csv[facility_id][3].to_int(),
            }
            for facility_id in range(min(len(FACILITY_NAMES), len(ability_csv)))
        ]

        equipment_data = getter.download("DataLocal", "equipmentlist.json")
        grade_data = getter.download("DataLocal", "equipmentgrade.csv")
        attribute_data = getter.download("resLocal", "attribute_explonation.tsv")
        effect_data = getter.download("resLocal", "equipment_explonation.tsv")
        if any(value is None for value in (equipment_data, grade_data, attribute_data, effect_data)):
            raise RuntimeError("本能玉データを取得できません")
        raw_orbs = core.JsonFile.from_data(equipment_data).as_object().get("ID", [])
        grade_csv = core.CSV(grade_data)
        attribute_csv = core.CSV(attribute_data, "\t")
        effect_csv = core.CSV(effect_data, "\t")
        orb_groups = {}
        for orb_id, raw_orb in enumerate(raw_orbs):
            grade_id = int(raw_orb.get("gradeID", 0))
            effect_id = int(raw_orb.get("content", 0))
            target_id = raw_orb.get("attribute")
            target_id = int(target_id) if target_id is not None else None
            key = (target_id, effect_id)
            if key not in orb_groups:
                target = ""
                if target_id is not None and 0 <= target_id < len(attribute_csv):
                    row = attribute_csv[target_id]
                    target = (row[1].to_str() if len(row) > 1 else row[0].to_str()).strip()
                effect = effect_csv[effect_id][0].to_str().split("%@", 1)[0].strip()
                orb_groups[key] = {
                    "name": f"{target} {effect}".strip(),
                    "target_id": target_id,
                    "effect_id": effect_id,
                    "ranks": [],
                }
            rank = grade_csv[grade_id][3].to_str().strip()
            orb_groups[key]["ranks"].append({"id": orb_id, "rank": rank, "grade_id": grade_id})
        metadata["talent_orbs"] = list(orb_groups.values())

        ticket_buy_data = getter.download("DataLocal", "Gatyaitembuy.csv")
        ticket_name_data = getter.download("resLocal", "GatyaitemName.csv")
        if ticket_buy_data is None or ticket_name_data is None:
            raise RuntimeError("イベントチケットデータを取得できません")
        ticket_buy_csv = core.CSV(ticket_buy_data)
        ticket_name_csv = core.CSV(ticket_name_data, core.Delimeter.from_country_code_res(cc))
        ticket_category_labels = {1: "イベント", 8: "福引", 10: "福引2"}
        event_tickets = []
        for item_id, row in enumerate(ticket_buy_csv.lines[1:]):
            if len(row) < 8:
                continue
            category = row[6].to_int()
            index = row[7].to_int()
            if category not in ticket_category_labels or index < 0:
                continue
            name = ticket_name_csv[item_id][0].to_str().strip() if item_id < len(ticket_name_csv) else ""
            comment = row[12].to_str().strip() if len(row) > 12 else ""
            purpose = comment or name or "名称不明チケット"
            if purpose == name:
                label = f"{name}（{ticket_category_labels[category]}保存枠{index + 1}）"
            else:
                label = f"{purpose}（{name or '名称不明チケット'}・{ticket_category_labels[category]}保存枠{index + 1}）"
            event_tickets.append({
                "id": f"{category}:{index}",
                "item_id": item_id,
                "category": category,
                "index": index,
                "name": name or "名称不明チケット",
                "purpose": purpose,
                "label": label,
            })
        # Gatyaitembuy.csvには過去イベントの保存枠も残り続ける。
        # 同名チケットはitem_idが最も新しい枠だけを採用し、最新版追加時に自動更新する。
        latest_event_tickets = {}
        for ticket in event_tickets:
            previous = latest_event_tickets.get(ticket["name"])
            priority = ("ID統一用" in ticket["purpose"], ticket["item_id"])
            previous_priority = (
                "ID統一用" in previous["purpose"], previous["item_id"]
            ) if previous else (False, -1)
            if priority > previous_priority:
                latest_event_tickets[ticket["name"]] = ticket
        event_tickets = sorted(latest_event_tickets.values(), key=lambda item: item["item_id"])
        for ticket in event_tickets:
            if "ID統一用" in ticket["purpose"]:
                ticket["label"] = f"{ticket['name']}（最新共通枠）"
            elif ticket["purpose"] != ticket["name"]:
                ticket["label"] = f"{ticket['purpose']}（{ticket['name']}・最新枠）"
            else:
                ticket["label"] = f"{ticket['name']}（最新枠）"
        metadata["event_tickets"] = event_tickets

        # 既存のVIP個別アイテムもGatyaitembuyの保存インデックスから生成する。
        # 新しいマタタビ等が追加された場合、HTMLの固定配列を更新せず追従できる。
        category_by_group = {
            "battle_items": 3,
            "catfruit": 4,
            "catseyes": 5,
            "catamins": 6,
            "base_materials": 7,
        }
        vip_item_groups = {}
        for group_key, category in category_by_group.items():
            labels_by_index = {}
            for item_id, row in enumerate(ticket_buy_csv.lines[1:]):
                if len(row) < 8 or row[6].to_int() != category:
                    continue
                item_index = row[7].to_int()
                if item_index < 0:
                    continue
                item_name = ticket_name_csv[item_id][0].to_str().strip() if item_id < len(ticket_name_csv) else ""
                labels_by_index[item_index] = item_name or f"{group_key}[{item_index}]"
            if labels_by_index:
                max_index = max(labels_by_index)
                fallback_labels = VIP_ITEM_LABELS.get(group_key, [])
                vip_item_groups[group_key] = [
                    labels_by_index.get(
                        item_index,
                        fallback_labels[item_index] if item_index < len(fallback_labels) else f"{group_key}[{item_index}]",
                    )
                    for item_index in range(max_index + 1)
                ]
        metadata["vip_item_groups"] = vip_item_groups
        _legend_metadata_cache = metadata
        _legend_metadata_cached_at = time.time()
        return metadata


LATEST_STAGE_CONTAINER_MINIMUMS = {
    "gauntlets": 82,
    "collab_gauntlets": 28,
    "zero_legend": 34,
}
LATEST_TALENT_ORB_COUNT = 310


def _character_form_counts():
    return {
        int(character["id"]): int(character["form_count"])
        for character in get_character_metadata().get("characters", [])
    }


def _character_true_form_states():
    return {
        int(character["id"]): max(0, min(2, int(character.get("true_form_state", 2))))
        for character in get_character_metadata().get("characters", [])
    }


def _latest_talent_orb_ids():
    try:
        ids = [
            int(rank["id"])
            for group in get_legend_metadata().get("talent_orbs", [])
            for rank in group.get("ranks", [])
        ]
        if ids:
            return sorted(set(ids))
    except Exception as e:
        print(f"[WARN] talent orb metadata fallback: {e}")
    return list(range(LATEST_TALENT_ORB_COUNT))


def _ensure_gauntlet_map(container, map_id):
    """BCSFEのGauntletChaptersへ未実装時の空マップを追加する。"""
    if map_id < 0 or not getattr(container, "chapters", None):
        return False
    first = container.chapters[0]
    if not first.chapters:
        return False
    total_stars = len(first.chapters)
    total_stages = len(first.chapters[0].stages)
    while len(container.chapters) <= map_id:
        chapter = type(first).init(total_stages, total_stars)
        for star_chapter in chapter.chapters:
            star_chapter.total_stages = total_stages
        container.chapters.append(chapter)
        if hasattr(container, "unknown"):
            container.unknown.append(0)
    return True


def _ensure_standard_chapter_map(container, map_id):
    """Chapters系（ネコビタン）へ最新版で増えたマップ枠を非破壊で追加する。"""
    chapters = getattr(container, "chapters", None)
    if map_id < 0 or not chapters:
        return False
    first = chapters[0]
    if not first.chapters:
        return False
    total_stars = len(first.chapters)
    total_stages = len(first.chapters[0].stages)
    while len(chapters) <= map_id:
        chapter = type(first).init(total_stages, total_stars)
        for star_chapter in chapter.chapters:
            star_chapter.total_stages = total_stages
        chapters.append(chapter)
    return True


def _ensure_latest_stage_slots(save, metadata=None):
    """15.5.1の既存ステージ機能に必要な保存枠を進行状態を保って補完する。"""
    targets = dict(LATEST_STAGE_CONTAINER_MINIMUMS)
    if metadata:
        for family_key, attribute in (
            ("gauntlets", "gauntlets"),
            ("collab_gauntlets", "collab_gauntlets"),
            ("behemoth", "behemoth_culling"),
            ("enigma", "enigma_clears"),
        ):
            maps = metadata.get("event_stage_families", {}).get(family_key, {}).get("maps", [])
            if maps:
                targets[attribute] = max(targets.get(attribute, 0), max(item["id"] for item in maps) + 1)
        zero_maps = metadata.get("zero_legend", {}).get("maps", [])
        if zero_maps:
            targets["zero_legend"] = max(targets["zero_legend"], max(item["id"] for item in zero_maps) + 1)

    for attribute in ("gauntlets", "collab_gauntlets", "behemoth_culling", "enigma_clears"):
        target_length = targets.get(attribute, 0)
        container = getattr(save, attribute, None)
        if container is not None and target_length:
            _ensure_gauntlet_map(container, target_length - 1)
    if metadata:
        catamin_maps = metadata.get("event_stage_families", {}).get("catamin", {}).get("maps", [])
        if catamin_maps:
            previous_length = len(save.catamin_stages.chapters.chapters)
            _ensure_standard_chapter_map(
                save.catamin_stages.chapters,
                max(item["id"] for item in catamin_maps),
            )
            added = len(save.catamin_stages.chapters.chapters) - previous_length
            if added > 0:
                save.catamin_stages.unknown.extend([0] * added)
        catclaw_maps = metadata.get("event_stage_families", {}).get("catclaw", {}).get("maps", [])
        if catclaw_maps and getattr(save, "dojo_chapters", None) is not None:
            save.dojo_chapters.create(max(item["id"] for item in catclaw_maps))
    if targets.get("zero_legend"):
        _ensure_zero_map(save, targets["zero_legend"] - 1)


def ensure_latest_save_schema(save):
    """旧15.4テンプレートを15.5.1互換へ非破壊で補完する。"""
    save.set_gv(core.GameVersion(TARGET_GAME_VERSION_NUMBER))
    # BCSFE 3.6.0で15.5.0から追加された保存フィールド。
    if not hasattr(save, "ub39"):
        save.ub39 = False

    metadata = get_character_metadata()
    characters = metadata.get("characters", [])
    target_cat_count = max((int(character["id"]) for character in characters), default=len(save.cats.cats))
    while len(save.cats.cats) < target_cat_count:
        save.cats.cats.append(core.Cat.init(len(save.cats.cats)))

    legend_metadata = None
    try:
        legend_metadata = get_legend_metadata()
    except Exception as e:
        print(f"[WARN] latest stage schema fallback: {e}")
    _ensure_latest_stage_slots(save, legend_metadata)

    # 長さ付き保存配列は、最新の既存アイテム数までゼロで拡張する。
    item_groups = (legend_metadata or {}).get("vip_item_groups", {})
    for attribute, group_key in (("catfruit", "catfruit"), ("catseyes", "catseyes"), ("catamins", "catamins")):
        target = len(item_groups.get(group_key, []))
        values = getattr(save, attribute, None)
        if isinstance(values, list) and target > len(values):
            values.extend([0] * (target - len(values)))
    materials = getattr(getattr(getattr(save, "ototo", None), "base_materials", None), "materials", None)
    target_materials = len(item_groups.get("base_materials", []))
    if isinstance(materials, list) and materials and target_materials > len(materials):
        material_type = type(materials[0])
        materials.extend(material_type.init() for _ in range(target_materials - len(materials)))

    ticket_arrays = {
        1: ("event_capsules", "event_capsules_counter"),
        8: ("lucky_tickets",),
        10: ("event_capsules_2",),
    }
    for category, attributes in ticket_arrays.items():
        category_tickets = [
            ticket for ticket in (legend_metadata or {}).get("event_tickets", [])
            if int(ticket.get("category", -1)) == category
        ]
        required_length = max((int(ticket["index"]) + 1 for ticket in category_tickets), default=0)
        for attribute in attributes:
            values = getattr(save, attribute, None)
            if isinstance(values, list) and required_length > len(values):
                values.extend([0] * (required_length - len(values)))
    return save


def _set_cat_form(save, cat, form_count, requested_form=None, true_form_state=None):
    """実装済み形態数を越えず、実機の自然な形態フラグで設定する。"""
    total_forms = max(1, min(4, int(form_count)))
    form = max(1, min(int(requested_form or total_forms), total_forms))
    if not cat.unlocked:
        cat.unlock(save)

    # BCSFEのset_form()/true_form()は、2形態しかないキャラにも
    # unlocked_forms=1以上を付ける経路がある。これは実機セーブの
    # 「2形態キャラ=current_form 1 / unlocked_forms 0」と一致しないため、
    # 形態数と選択形態から3フィールドを必ず一組で検証する。
    old_current = max(0, int(cat.current_form))
    old_unlocked = max(0, int(cat.unlocked_forms))
    old_fourth = int(cat.fourth_form)
    cat.current_form = form - 1
    if total_forms == 1:
        cat.unlocked_forms = 0
        cat.fourth_form = 0
    elif total_forms == 2:
        cat.unlocked_forms = 0
        cat.fourth_form = 0
    elif form == 4:
        cat.unlocked_forms = max(0, min(2, int(true_form_state if true_form_state is not None else 2)))
        cat.fourth_form = 2
    elif form == 3:
        cat.unlocked_forms = max(0, min(2, int(true_form_state if true_form_state is not None else 2)))
        cat.fourth_form = 0 if total_forms == 3 else max(0, min(old_fourth, 2))
    elif total_forms == 3:
        cat.unlocked_forms = min(old_unlocked, 3)
        cat.fourth_form = 0
    elif old_fourth == 2 or old_current == 3:
        cat.unlocked_forms = min(old_unlocked, 3)
        cat.fourth_form = 2
    else:
        cat.unlocked_forms = min(old_unlocked, 3)
        cat.fourth_form = max(0, min(old_fourth, 1))
    return form


def _set_cat_latest_form(save, cat, form_counts=None, true_form_states=None):
    counts = form_counts or _character_form_counts()
    total_forms = counts.get(cat.id + 1)
    if total_forms is None:
        # 配布metadataより新しいキャラを1形態と決めつけて壊さない。
        return None
    states = true_form_states or _character_true_form_states()
    return _set_cat_form(save, cat, total_forms, true_form_state=states.get(cat.id + 1, 2))


def _normalise_cat_form_flags(save, form_counts=None):
    """既存セーブに残った未実装形態・余分な進化権を安全に補正する。

    現在形態を可能な限り保ちつつ、実装形態数を越える値だけを縮める。
    第3/第4形態を既に解放済みで現在は下位形態を使用している状態は保持する。
    """
    counts = form_counts or _character_form_counts()
    repaired = 0
    for cat in save.cats.cats:
        if cat.id + 1 not in counts:
            # 新版で追加された未知キャラは、metadataが追いつくまで現状を保つ。
            continue
        total_forms = max(1, min(4, int(counts[cat.id + 1])))
        before = (
            int(cat.current_form),
            int(cat.unlocked_forms),
            int(cat.fourth_form),
        )

        current_form = max(0, min(int(cat.current_form), total_forms - 1))
        unlocked_forms = max(0, int(cat.unlocked_forms))
        fourth_form = int(cat.fourth_form)

        if total_forms == 1:
            current_form = unlocked_forms = fourth_form = 0
        elif total_forms == 2:
            # 2形態キャラの第2形態は進化権を使用しない。
            unlocked_forms = 0
            fourth_form = 0
        elif total_forms == 3:
            # 第三形態のunlocked_formsは取得経路により0/1/2/3があり得る。
            # 推測で引き上げず、未実装の第4形態フラグだけを除去する。
            unlocked_forms = min(unlocked_forms, 3)
            fourth_form = 0
        else:
            # fourth_form=2 または実際に第4形態を使用中なら解放済み。
            has_fourth = fourth_form == 2 or current_form == 3
            if has_fourth:
                unlocked_forms = min(unlocked_forms, 3)
                fourth_form = 2
            else:
                current_form = min(current_form, 2)
                unlocked_forms = min(unlocked_forms, 3)
                fourth_form = max(0, min(fourth_form, 1))

        after = (current_form, unlocked_forms, fourth_form)
        if after != before:
            cat.current_form, cat.unlocked_forms, cat.fourth_form = after
            repaired += 1
    return repaired


def _talent_definitions_by_cat():
    """画面と適用処理が同じ最新JP本能定義を使うための索引。"""
    return {
        int(character["id"]): {
            int(talent["id"]): talent for talent in character.get("talents", [])
        }
        for character in get_character_metadata().get("characters", [])
        if character.get("talents")
    }


def _set_cat_talent_level(cat, ability_id, level):
    if cat.talents is None:
        cat.talents = []
    talent = next((item for item in cat.talents if item.id == ability_id), None)
    if talent is None:
        cat.talents.append(Talent(ability_id, level))
    else:
        talent.level = level


def _apply_character_talents(cat, display_id, setting, talent_definitions):
    """指定キャラの実装済み本能だけを設定。自然上限を越える値も保持する。"""
    definitions = talent_definitions.get(display_id, {})
    if not definitions:
        return 0
    action = setting.get("talent_action", "set")
    if action == "disable_all":
        if cat.talents is None:
            return 0
        for talent in cat.talents:
            talent.level = 0
        return len(cat.talents)
    levels = setting.get("talents", {})
    applied = 0
    for talent_id, requested_level in levels.items():
        ability_id = int(talent_id)
        if ability_id not in definitions:
            continue
        level = 0 if action == "disable_selected" else max(0, min(32767, int(requested_level)))
        _set_cat_talent_level(cat, ability_id, level)
        applied += 1
    return applied


def _latest_rank_gift_thresholds():
    """最新JP rankGift.csvを数値版で読み、(保存index, 必要UR)を返す。"""
    getter = _latest_jp_game_data_getter()
    data = getter.download("DataLocal", "rankGift.csv")
    if data is None:
        raise RuntimeError("ユーザーランク報酬定義を取得できません")
    return [
        (index, row[0].to_int())
        for index, row in enumerate(core.CSV(data).lines)
        if len(row)
    ]


def _set_all_user_rank_rewards(save, claimed):
    """現在到達済みUR報酬を一括変更し、未来報酬は未受取のままにする。"""
    thresholds = _latest_rank_gift_thresholds()
    required = max((index + 1 for index, _ in thresholds), default=0)
    while len(save.user_rank_rewards.rewards) < required:
        save.user_rank_rewards.rewards.append(Reward.init())
    user_rank = save.calculate_user_rank()
    original = [reward.claimed for reward in save.user_rank_rewards.rewards]
    for reward in save.user_rank_rewards.rewards:
        reward.claimed = False
    for index, threshold in thresholds:
        if claimed and threshold <= user_rank:
            save.user_rank_rewards.rewards[index].claimed = True
    changed = sum(
        before != reward.claimed
        for before, reward in zip(original, save.user_rank_rewards.rewards)
    )
    return changed, sum(threshold <= user_rank for _, threshold in thresholds)


def _set_all_catguide_rewards(save, claimed):
    """受取化は所持キャラ、未受取化は全保存枠を対象にする。"""
    changed = 0
    targets = [cat for cat in save.cats.cats if cat.unlocked] if claimed else save.cats.cats
    for cat in targets:
        if cat.catguide_collected != bool(claimed):
            cat.catguide_collected = bool(claimed)
            changed += 1
    return changed, len(targets)


def _complete_all_defined_missions(save):
    """最新JP定義のメイン・スペシャル・週・月ミッションを全て達成状態へする。"""
    getter = _latest_jp_game_data_getter()
    data = getter.download("DataLocal", "Mission_Condition.csv")
    if data is None:
        raise RuntimeError("ミッション定義を取得できません")
    # 配信終了済みだがセーブに残っているミッションも取りこぼさない。
    seen = set(save.missions.clear_states)
    for mission_id in seen:
        save.missions.clear_states[mission_id] = 2
    for row in core.CSV(data).lines:
        if len(row) < 4:
            continue
        if not row[0].to_str().strip().lstrip("-").isdigit():
            continue
        mission_id = row[0].to_int()
        mission_type = row[1].to_int()
        seen.add(mission_id)
        save.missions.clear_states[mission_id] = 2
        save.missions.requirements[mission_id] = max(0, row[3].to_int())
        # この辞書は週次だけでなく、現在表示済みの期間ミッションIDも保持する。
        if mission_type in {1, 2, 3}:
            save.missions.weekly_missions[mission_id] = True
    return len(seen)


def validate_legend_stages_shape(data):
    """legend_stagesの構造と総選択数を軽量検証する。"""
    raw = data.get("legend_stages", {})
    if not isinstance(raw, dict) or any(key not in LEGEND_SERIES for key in raw):
        return False
    count = 0
    for maps in raw.values():
        if not isinstance(maps, dict) or len(maps) > 100:
            return False
        for stars in maps.values():
            if not isinstance(stars, dict) or len(stars) > 4:
                return False
            for stages in stars.values():
                if not isinstance(stages, list) or len(stages) > 12:
                    return False
                count += len(stages)
                if count > MAX_LEGEND_SELECTIONS:
                    return False
    return True


def validate_detailed_stage_settings_shape(data):
    """メイン・イベントのステージ別クリア回数のネストと総件数を検証する。"""
    total = 0
    main_raw = data.get("main_story_stages")
    if main_raw is not None:
        if not isinstance(main_raw, dict) or len(main_raw) > len(MAIN_STORY_REAL_INDEX):
            return False
        for stages in main_raw.values():
            if not isinstance(stages, dict) or len(stages) > 48:
                return False
            total += len(stages)

    event_raw = data.get("event_stage_settings")
    if event_raw is not None:
        if not isinstance(event_raw, dict) or any(key not in EVENT_STAGE_FAMILIES for key in event_raw):
            return False
        for family_key, maps in event_raw.items():
            if not isinstance(maps, dict) or len(maps) > 1000:
                return False
            for stars in maps.values():
                if not isinstance(stars, dict) or len(stars) > 4:
                    return False
                for stages in stars.values():
                    max_stages = 256 if family_key == "labyrinth" else 64
                    if not isinstance(stages, dict) or len(stages) > max_stages:
                        return False
                    total += len(stages)
    return total <= MAX_DETAILED_STAGE_SELECTIONS


def validate_labyrinth_character_settings_shape(data):
    """地底迷宮の封印・解除指定の型と件数だけを先に検証する。"""
    raw = data.get("labyrinth_characters")
    if raw is None:
        return True
    if not isinstance(raw, dict) or raw.get("action") not in LABYRINTH_CHARACTER_ACTIONS:
        return False
    ids = raw.get("ids", [])
    if not isinstance(ids, list) or len(ids) > MAX_LABYRINTH_CHARACTERS:
        return False
    try:
        return all(1 <= int(cat_id) <= 9999 for cat_id in ids)
    except (TypeError, ValueError):
        return False


def validate_lineup_settings_shape(data):
    """VIP編成設定の型を検証する。キャラ番号は画面と同じ1始まり、空枠はNone。"""
    raw = data.get("lineup_settings")
    if raw is None:
        return True
    if not isinstance(raw, dict):
        return False
    cats = raw.get("cats")
    forms = raw.get("forms")
    if not isinstance(cats, list) or len(cats) != 10 or not isinstance(forms, list) or len(forms) != 10:
        return False
    try:
        lineup_number = int(raw.get("lineup", 1))
        if not 1 <= lineup_number <= 20:
            return False
        return (
            all(cat_id is None or 1 <= int(cat_id) <= 9999 for cat_id in cats)
            and all(form is None or 1 <= int(form) <= 4 for form in forms)
        )
    except (TypeError, ValueError):
        return False


def validate_score_settings_shape(data):
    """VIP限定の道場・未来編スコア指定の型と件数を検証する。"""
    dojo = data.get("dojo_score_settings")
    if dojo is not None:
        if not isinstance(dojo, dict) or set(dojo) - {"hall_of_initiates"}:
            return False
        try:
            if not all(0 <= int(value) <= 2_147_483_647 for value in dojo.values()):
                return False
        except (TypeError, ValueError):
            return False

    future = data.get("future_score_settings")
    if future is not None:
        if not isinstance(future, dict) or len(future) > 3:
            return False
        try:
            if any(int(position) not in {3, 4, 5} for position in future):
                return False
            if not all(0 <= int(value) <= 9999 for value in future.values()):
                return False
        except (TypeError, ValueError):
            return False
    return True


def safe_dojo_score_settings(data):
    """BCSFEで保存可能な常設道場（入門の間）のスコアだけを返す。"""
    raw = data.get("dojo_score_settings")
    if not isinstance(raw, dict) or "hall_of_initiates" not in raw:
        return None
    try:
        score = max(0, min(2_147_483_647, int(raw["hall_of_initiates"])))
    except (TypeError, ValueError):
        return None
    return {"hall_of_initiates": score}


def safe_future_score_settings(data):
    """画面上の未来編1～3章（位置3～5）を0～9999へ正規化する。"""
    raw = data.get("future_score_settings")
    if not isinstance(raw, dict):
        return None
    output = {}
    for raw_position, raw_score in list(raw.items())[:3]:
        try:
            position = int(raw_position)
            score = max(0, min(9999, int(raw_score)))
        except (TypeError, ValueError):
            continue
        if position in {3, 4, 5}:
            output[position] = score
    return output or None


def safe_lineup_settings(data):
    """編成番号と10枠を、最新版キャラmetadataに照合して正規化する。"""
    raw = data.get("lineup_settings")
    if not isinstance(raw, dict):
        return None
    try:
        characters = get_character_metadata().get("characters", [])
        form_counts = {
            int(character["id"]): int(character.get("form_count", 1))
            for character in characters if character.get("selectable", True)
        }
        valid_ids = set(form_counts)
    except Exception:
        valid_ids = set()
        form_counts = {}
    try:
        lineup_number = max(1, min(20, int(raw.get("lineup", 1))))
    except (TypeError, ValueError):
        lineup_number = 1
    cats = []
    for raw_id in raw.get("cats", [])[:10]:
        if raw_id is None:
            cats.append(None)
            continue
        try:
            cat_id = int(raw_id)
        except (TypeError, ValueError):
            cats.append(None)
            continue
        cats.append(cat_id if (not valid_ids or cat_id in valid_ids) else None)
    cats.extend([None] * (10 - len(cats)))
    forms = []
    for index, raw_form in enumerate(raw.get("forms", [])[:10]):
        cat_id = cats[index] if index < len(cats) else None
        if raw_form is None:
            forms.append(None)
            continue
        try:
            requested = int(raw_form)
        except (TypeError, ValueError):
            requested = 1
        forms.append(max(1, min(requested, form_counts.get(cat_id, 4))))
    forms.extend([None] * (10 - len(forms)))
    # 形態はキャラ単位の保存値。同じキャラで混在した場合は高い形態を優先する。
    final_forms = {}
    for cat_id, form in zip(cats, forms):
        if cat_id is not None and form is not None:
            final_forms[cat_id] = max(final_forms.get(cat_id, 1), form)
    forms = [final_forms.get(cat_id) for cat_id in cats]
    return {"lineup": lineup_number, "cats": cats, "forms": forms}


def safe_legend_stages(data):
    """章→星→ステージの選択をbcsfeメタデータに照合して正規化する。"""
    raw = data.get("legend_stages", {})
    if not isinstance(raw, dict):
        return {}
    try:
        metadata = get_legend_metadata()
    except Exception as e:
        print(f"[ERROR] legend metadata: {e}")
        return {}

    result = {}
    for series_key, raw_maps in raw.items():
        if series_key not in LEGEND_SERIES or not isinstance(raw_maps, dict):
            continue
        map_specs = {m["id"]: m for m in metadata.get(series_key, {}).get("maps", [])}
        clean_maps = {}
        for raw_map_id, raw_stars in raw_maps.items():
            try:
                map_id = int(raw_map_id)
            except (TypeError, ValueError):
                continue
            map_spec = map_specs.get(map_id)
            if map_spec is None or not isinstance(raw_stars, dict):
                continue
            clean_stars = {}
            for raw_star, raw_stages in raw_stars.items():
                try:
                    star = int(raw_star)
                except (TypeError, ValueError):
                    continue
                if not 0 <= star < map_spec["crowns"] or not isinstance(raw_stages, list):
                    continue
                stages = sorted({
                    int(stage) for stage in raw_stages
                    if str(stage).lstrip("-").isdigit() and 0 <= int(stage) < len(map_spec["stages"])
                })
                if stages:
                    clean_stars[star] = stages
            if clean_stars:
                clean_maps[map_id] = clean_stars
        # 空dictも「親は選択済みだが詳細は全解除」として保持する。
        result[series_key] = clean_maps
    return result


def full_legend_selection(series_key):
    """指定シリーズの実装済み章・冠・ステージをすべて選択した形にする。"""
    metadata = get_legend_metadata().get(series_key, {})
    maps = {}
    for map_spec in metadata.get("maps", []):
        maps[map_spec["id"]] = {
            star: list(range(len(map_spec["stages"])))
            for star in range(map_spec["crowns"])
        }
    return {series_key: maps}


def safe_vip_facilities(data):
    raw = data.get("vip_facilities", {})
    if not isinstance(raw, dict):
        return {}
    try:
        specs = {item["id"]: item for item in get_legend_metadata().get("facilities", [])}
    except Exception as e:
        print(f"[ERROR] facility metadata: {e}")
        return {}
    result = {}
    for raw_id, raw_level in raw.items():
        try:
            facility_id, level = int(raw_id), int(raw_level)
        except (TypeError, ValueError):
            continue
        spec = specs.get(facility_id)
        if spec is not None:
            # VIPの「施設 指定」は通常の+上限を超える値も許可する。
            # 基礎Lvは適用時に正規上限へ収め、残りをすべて+値へ回す。
            result[facility_id] = max(1, level)
    return result


def safe_vip_talent_orbs(data):
    raw = data.get("vip_talent_orbs", {})
    if not isinstance(raw, dict):
        return {}
    try:
        valid_ids = {
            rank["id"]
            for group in get_legend_metadata().get("talent_orbs", [])
            for rank in group.get("ranks", [])
        }
    except Exception as e:
        print(f"[ERROR] talent orb metadata: {e}")
        return {}
    result = {}
    for raw_id, raw_amount in raw.items():
        try:
            orb_id, amount = int(raw_id), int(raw_amount)
        except (TypeError, ValueError):
            continue
        if orb_id in valid_ids:
            result[orb_id] = max(0, min(amount, 998))
    return result


def apply_vip_facilities(save, facilities):
    logs = []
    if facilities is None:
        return logs
    try:
        specs = {int(item["id"]): item for item in get_legend_metadata().get("facilities", [])}
        valid_skills = save.special_skills.get_valid_skills()
        for raw_facility_id, raw_value in (facilities or {}).items():
            try:
                facility_id = int(raw_facility_id)
            except (TypeError, ValueError):
                continue
            if facility_id < 0 or facility_id > 9 or facility_id >= len(valid_skills) or facility_id not in specs:
                continue

            spec = specs[facility_id]
            if isinstance(raw_value, dict):
                # 新UI: 基礎Lvと+値を完全に分離して指定。
                base_level = max(0, min(int(raw_value.get("base", 0)), int(spec.get("max_base", 0))))
                plus_level = max(0, min(int(raw_value.get("plus", 0)), int(spec.get("max_plus", 0))))
            else:
                # 旧形式との互換: 合計Lvを基礎Lv/+値へ分解。
                total_level = max(0, int(raw_value))
                base_level = min(total_level, int(spec.get("max_base", 0)))
                plus_level = max(0, total_level - int(spec.get("max_base", 0)))
                plus_level = min(plus_level, int(spec.get("max_plus", 0)))

            valid_skills[facility_id].upgrade.base = max(base_level - 1, 0)
            valid_skills[facility_id].upgrade.plus = plus_level

            if facility_id == 0 and len(save.special_skills.skills) > 1:
                save.special_skills.skills[1].upgrade.base = max(base_level - 1, 0)
                save.special_skills.skills[1].upgrade.plus = plus_level

            logs.append(f"{spec['name']}(基礎Lv.{base_level} / ＋{plus_level})")
    except Exception as e:
        print(f"[ERROR] vip facilities: {e}")
    return logs


def apply_vip_talent_orbs(save, talent_orbs):
    logs = []
    for orb_id, amount in (talent_orbs or {}).items():
        try:
            save.talent_orbs.set_orb(orb_id, amount)
            logs.append(f"本能玉ID{orb_id}({amount})")
        except Exception as e:
            print(f"[ERROR] vip talent orb {orb_id}: {e}")
    if logs:
        return [f"本能玉({len(logs)}種類)"]
    return []


def _ensure_zero_map(save, map_id):
    """古いテンプレートにも最新の零レジェンド章スロットを安全に追加する。"""
    chapters = save.zero_legends.chapters
    if not chapters:
        return False
    while len(chapters) <= map_id:
        chapters.append(copy.deepcopy(chapters[0]))
        for chapter in chapters[-1].chapters:
            chapter.selected_stage = 0
            chapter.clear_progress = 0
            chapter.unlock_state = 0
            if hasattr(chapter, "chapter_unlock_state"):
                chapter.chapter_unlock_state = 0
            for stage in chapter.stages:
                stage.clear_times = 0
    return True


def _sync_idi_clear(save):
    """古代研究所★4クリア時にイディ関連の取得状態を矛盾なく揃える。"""
    try:
        idi = save.cats.get_cat_by_id(568)
        if idi:
            idi.unlock(save)
        elif len(save.unit_drops) > 202:
            save.unit_drops[202] = 1
    except Exception as e:
        print(f"[ERROR] idi unlock: {e}")
    try:
        save.medals.add_medal(86)  # 【古代生命体撃破】
    except Exception as e:
        print(f"[ERROR] idi medal: {e}")
    try:
        # RE_026「太古の力」の報酬取得状態。配列があるバージョンだけ同期する。
        reward = save.item_reward_stages.sub_chapters[26].sub_chapters[0].stages[0]
        reward.claimed = True
    except (AttributeError, IndexError):
        pass


def apply_legend_stages(save, selections):
    """選択された章・冠・ステージだけをクリアする。"""
    logs = []
    for series_key, maps in (selections or {}).items():
        applied = 0
        for raw_map_id, stars in maps.items():
            try: map_id=int(raw_map_id)
            except (TypeError,ValueError): continue
            for raw_star, stage_ids in stars.items():
                try: star=int(raw_star)
                except (TypeError,ValueError): continue
                for raw_stage_id in stage_ids:
                    try: stage_id=int(raw_stage_id)
                    except (TypeError,ValueError): continue
                    try:
                        if series_key == "legend":
                            crown_chapters = save.event_stages.chapters[0].chapters[map_id].chapters
                        elif series_key == "true_legend":
                            crown_chapters = save.uncanny.chapters.chapters[map_id].chapters
                        elif series_key == "zero_legend":
                            if not _ensure_zero_map(save, map_id):
                                continue
                            crown_chapters = save.zero_legends.chapters[map_id].chapters
                        else:
                            continue

                        chapter = crown_chapters[star]
                        if stage_id >= len(chapter.stages):
                            continue

                        # 新規アカウントではレジェンド系の星別進行データが未初期化のことがあり、
                        # いきなり4冠(star=3)だけを書き込むと、保存上は通常の「クリア」だけに
                        # 見える場合がある。選択冠より下の冠を同ステージで先に初期化・クリアし、
                        # その後に目的の冠を設定して、初回適用でも冠情報が保存されるようにする。
                        for prerequisite_star in range(star):
                            prerequisite = crown_chapters[prerequisite_star]
                            if stage_id >= len(prerequisite.stages):
                                continue
                            if hasattr(prerequisite, "chapter_unlock_state"):
                                prerequisite.chapter_unlock_state = 3
                            if hasattr(prerequisite, "unlock_state"):
                                prerequisite.unlock_state = 3
                            prerequisite.clear_progress = max(prerequisite.clear_progress, stage_id + 1)
                            prerequisite.stages[stage_id].clear_stage(1, ensure_cleared_only=True)

                        if hasattr(chapter, "chapter_unlock_state"):
                            chapter.chapter_unlock_state = 3
                        if hasattr(chapter, "unlock_state"):
                            chapter.unlock_state = 3
                        chapter.clear_progress = max(chapter.clear_progress, stage_id + 1)
                        chapter.stages[stage_id].clear_stage(1, ensure_cleared_only=True)
                        applied += 1
                    except (AttributeError, IndexError, TypeError) as e:
                        print(f"[ERROR] {series_key}[{map_id}][{star}][{stage_id}]: {e}")

        if applied:
            label = LEGEND_SERIES[series_key]["label"]
            logs.append(f"{label}({applied}ステージ冠)")

    # レジェンド最終章「古代研究所」★4「太古の力」を選んだ時だけ同期する。
    idi_stages = selections.get("legend", {}).get(48, {}).get(3, []) if selections else []
    if 0 in idi_stages:
        _sync_idi_clear(save)
        logs.append("イディ取得・撃破済み")
    return logs


def safe_main_story_chapters(data):
    """main_story_chapters を検証済みの整数リスト(表示ポジション0〜8)として返す。不正・未指定なら None(=全章)。"""
    raw = data.get("main_story_chapters")
    if raw is None:
        return None
    if not isinstance(raw, list):
        return None
    try:
        indices = sorted({int(v) for v in raw if 0 <= int(v) <= 8})
    except (TypeError, ValueError):
        return None
    return indices if indices else None


def _safe_clear_count(value):
    try:
        return max(1, min(MAX_STAGE_CLEAR_COUNT, int(value)))
    except (TypeError, ValueError):
        return 1


def safe_main_story_stages(data):
    """章→ステージ→クリア回数。キーが存在する空辞書も親の全クリアを抑止する。"""
    if "main_story_stages" not in data:
        return None
    raw = data.get("main_story_stages")
    if not isinstance(raw, dict):
        return {}
    result = {}
    for raw_position, raw_stages in raw.items():
        try:
            position = int(raw_position)
        except (TypeError, ValueError):
            continue
        if not 0 <= position < len(MAIN_STORY_REAL_INDEX) or not isinstance(raw_stages, dict):
            continue
        stages = {}
        for raw_stage, raw_count in raw_stages.items():
            try:
                stage = int(raw_stage)
            except (TypeError, ValueError):
                continue
            if 0 <= stage < 48:
                stages[stage] = _safe_clear_count(raw_count)
        result[position] = stages
    return result


def safe_event_stage_settings(data):
    """イベント種別→マップ→冠→ステージ→クリア回数を安全な整数へ整形する。"""
    labyrinth_characters = safe_labyrinth_character_settings(data)
    if "event_stage_settings" not in data and labyrinth_characters is None:
        return None
    raw = data.get("event_stage_settings")
    if not isinstance(raw, dict):
        raw = {}
    result = {}
    for family_key, raw_maps in raw.items():
        if family_key not in EVENT_STAGE_FAMILIES or not isinstance(raw_maps, dict):
            continue
        maps = {}
        for raw_map, raw_stars in raw_maps.items():
            try:
                map_id = int(raw_map)
            except (TypeError, ValueError):
                continue
            if not 0 <= map_id < 1000 or not isinstance(raw_stars, dict):
                continue
            stars = {}
            for raw_star, raw_stages in raw_stars.items():
                try:
                    star = int(raw_star)
                except (TypeError, ValueError):
                    continue
                if not 0 <= star < 4 or not isinstance(raw_stages, dict):
                    continue
                stages = {}
                for raw_stage, raw_count in raw_stages.items():
                    try:
                        stage = int(raw_stage)
                    except (TypeError, ValueError):
                        continue
                    max_stages = 256 if family_key == "labyrinth" else 64
                    if 0 <= stage < max_stages:
                        stages[stage] = _safe_clear_count(raw_count)
                if stages:
                    stars[star] = stages
            if stars:
                maps[map_id] = stars
        result[family_key] = maps
    if labyrinth_characters is not None:
        result["_labyrinth_characters"] = labyrinth_characters
    return result


def safe_labyrinth_character_settings(data):
    """画面表示と同じ1始まりのキャラ番号を重複なしで正規化する。"""
    raw = data.get("labyrinth_characters")
    if not isinstance(raw, dict):
        return None
    action = raw.get("action")
    if action not in LABYRINTH_CHARACTER_ACTIONS:
        return None
    ids = []
    seen = set()
    for raw_id in raw.get("ids", [])[:MAX_LABYRINTH_CHARACTERS]:
        try:
            display_id = max(1, min(9999, int(raw_id)))
        except (TypeError, ValueError):
            continue
        if display_id in seen:
            continue
        seen.add(display_id)
        ids.append(display_id)
    if action.endswith("_selected") and not ids:
        return None
    return {"action": action, "ids": ids}


def safe_special_stages(data):
    """ゾンビ襲来・魔界編の詳細選択を検証する。空選択も親処理を抑止するため保持する。"""
    raw = data.get("special_stages")
    if not isinstance(raw, dict):
        return None
    result = {}
    if "zombie" in raw:
        zombie_raw = raw.get("zombie")
        zombie = {}
        if isinstance(zombie_raw, dict):
            for raw_chapter, raw_stages in zombie_raw.items():
                try:
                    chapter = int(raw_chapter)
                except (TypeError, ValueError):
                    continue
                if not 0 <= chapter < len(MAIN_STORY_REAL_INDEX) or not isinstance(raw_stages, list):
                    continue
                try:
                    zombie[chapter] = sorted({int(stage) for stage in raw_stages if 0 <= int(stage) < 48})
                except (TypeError, ValueError):
                    zombie[chapter] = []
        result["zombie"] = zombie
    if "aku" in raw:
        aku_raw = raw.get("aku")
        if isinstance(aku_raw, list):
            try:
                result["aku"] = sorted({int(stage) for stage in aku_raw if 0 <= int(stage) < 64})
            except (TypeError, ValueError):
                result["aku"] = []
        else:
            result["aku"] = []
    if "aku_ex" in raw:
        aku_ex_raw = raw.get("aku_ex")
        if isinstance(aku_ex_raw, list):
            try:
                result["aku_ex"] = sorted({int(stage) for stage in aku_ex_raw if int(stage) == 0})
            except (TypeError, ValueError):
                result["aku_ex"] = []
        else:
            result["aku_ex"] = []
    return result


def _sync_jagando_clear(save):
    """富士山EX（破壊神ジャガンドー）のクリア・報酬・キャラ取得を同期する。"""
    try:
        save.event_stages.clear_stage(
            1, 42, 0, 0, clear_amount=1, ensure_cleared_only=True
        )
    except (AttributeError, IndexError) as e:
        print(f"[ERROR] jagando stage: {e}")
    try:
        jagando_jr = save.cats.get_cat_by_id(622)
        if jagando_jr:
            jagando_jr.unlock(save)
    except Exception as e:
        print(f"[ERROR] jagando jr unlock: {e}")
    try:
        reward = save.item_reward_stages.sub_chapters[42].sub_chapters[0].stages[0]
        reward.claimed = True
    except (AttributeError, IndexError):
        pass


def apply_main_story_stages(save, selections):
    """選択されたメインステージだけを指定回数クリアし、お宝を最高にする。"""
    logs = []
    if selections is None:
        return logs
    applied = 0
    for position, stages in selections.items():
        if not 0 <= position < len(MAIN_STORY_REAL_INDEX):
            continue
        real_id = MAIN_STORY_REAL_INDEX[position]
        if real_id >= len(save.story.chapters):
            continue
        chapter = save.story.chapters[real_id]
        for stage_id, clear_count in stages.items():
            if stage_id >= min(48, len(chapter.stages)):
                continue
            try:
                chapter.clear_stage(stage_id, clear_count)
                chapter.stages[stage_id].treasure = 3
                applied += 1
            except (AttributeError, IndexError) as e:
                print(f"[ERROR] main_story_stages[{position}][{stage_id}]: {e}")
    if applied:
        logs.append(f"メイン詳細({applied}ステージ)")
    return logs


def apply_dojo_score_settings(save, settings):
    """常設道場の保存領域へスコアを設定する（BCSFEの道場編集と同じ0:0）。"""
    if not settings:
        return []
    try:
        score = int(settings["hall_of_initiates"])
        save.dojo.chapters.get_stage(0, 0).score = score
        return [f"道場・入門の間スコア({score})"]
    except (AttributeError, KeyError, TypeError, ValueError) as e:
        print(f"[ERROR] dojo score: {e}")
        return []


def apply_future_score_settings(save, settings):
    """未来編1〜3章の一括・個別採点スコアを保存する。"""
    if not settings: return []
    logs=[]
    for position, score in settings.items():
        try:
            position=int(position)
            if position not in {3,4,5}: continue
            real_id=MAIN_STORY_REAL_INDEX[position]; chapter=save.story.chapters[real_id]
            stages=chapter.get_valid_treasure_stages()
            if isinstance(score,dict) and "individual" in score:
                values=score["individual"]
                for sid, raw in enumerate(values):
                    if sid < len(stages): stages[sid].itf_timed_score=int(raw)
                logs.append(f"{MAIN_STORY_CHAPTER_LABELS[position]}個別採点スコア({len(values)}ステージ)")
            else:
                value=int(score)
                for stage in stages: stage.itf_timed_score=value
                logs.append(f"{MAIN_STORY_CHAPTER_LABELS[position]}採点スコア({value}・{len(stages)}ステージ)")
        except (AttributeError,IndexError,TypeError,ValueError) as e:
            print(f"[ERROR] future score chapter {position}: {e}")
    return logs

def _labyrinth_value(save, names, default=None):
    """BCSFEが地底迷宮へ正式名を付けた後も、現行の未命名フィールドへ後方互換する。"""
    owners = [getattr(save, "labyrinth", None), save]
    for owner in owners:
        if owner is None:
            continue
        for name in names:
            if hasattr(owner, name):
                return getattr(owner, name)
    return default


def _set_labyrinth_value(save, names, value):
    owners = [getattr(save, "labyrinth", None), save]
    changed = False
    for owner in owners:
        if owner is None:
            continue
        for name in names:
            if hasattr(owner, name):
                setattr(owner, name, value.copy() if isinstance(value, list) else value)
                changed = True
    return changed


def _labyrinth_unlocked_cat_ids(save):
    return {
        int(cat.id) for cat in getattr(getattr(save, "cats", None), "cats", [])
        if bool(getattr(cat, "unlocked", False))
    }


def _sync_labyrinth_remaining(save, trapped=None, active=None):
    trapped = set(trapped if trapped is not None else _labyrinth_value(
        save, ("trapped_cats", "sealed_cats", "unavailable_cats", "ushl3"), []
    ))
    active = set(active if active is not None else _labyrinth_value(
        save, ("active_cats", "current_cats", "surviving_cats", "ushl4"), []
    ))
    unlocked = _labyrinth_unlocked_cat_ids(save)
    remaining = max(0, len(unlocked - trapped - active))
    _set_labyrinth_value(save, ("available_cat_count", "remaining_cat_count", "ush6"), remaining)
    _set_labyrinth_value(save, ("available_cat_count_2", "remaining_cat_count_2", "ush8"), remaining)
    return remaining


def _remove_labyrinth_lineup_cats(save, cat_ids):
    """地底迷宮専用編成（現行セーブではスロット20）から封印対象だけを外す。"""
    if not cat_ids:
        return
    try:
        slots = save.lineups.slots[20].slots
    except (AttributeError, IndexError):
        return
    encoded_ids = {cat_id + 2 for cat_id in cat_ids}
    for slot in slots:
        if getattr(slot, "cat_id", -1) in encoded_ids:
            slot.cat_id = -1


def apply_lineup_settings(save, settings):
    """通常編成1〜20の指定された10枠を書き換える。同一キャラの重複も保持する。"""
    if not settings:
        return []
    try:
        lineup_index = int(settings.get("lineup", 1)) - 1
        lineups = getattr(getattr(save, "lineups", None), "slots", [])
        # 現行セーブの21番目は地底迷宮専用。通常編成としては1〜20だけを扱う。
        if not 0 <= lineup_index < min(20, len(lineups)):
            return ["編成設定エラー(指定編成が存在しません)"]
        slots = lineups[lineup_index].slots
        cat_ids = list(settings.get("cats", []))[:10]
        cat_ids.extend([None] * (10 - len(cat_ids)))
        forms = list(settings.get("forms", []))[:10]
        forms.extend([None] * (10 - len(forms)))
        form_counts = _character_form_counts()
        true_form_states = _character_true_form_states()
        applied = 0
        for slot_index, display_id in enumerate(cat_ids):
            if slot_index >= len(slots):
                break
            if display_id is None:
                slots[slot_index].cat_id = -1
                continue
            display_id = int(display_id)
            cat = save.cats.get_cat_by_id(display_id - 1)
            if cat is None:
                slots[slot_index].cat_id = -1
                continue
            # 編成だけを設定する操作で外部ゲームデータ取得を発生させない。
            # 未解放キャラが選ばれた場合も編成が無効化されないよう必要フラグを立てる。
            cat.unlocked = 1
            cat.gatya_seen = 1
            if forms[slot_index] is not None:
                _set_cat_form(
                    save, cat, form_counts.get(display_id, 1), forms[slot_index],
                    true_form_states.get(display_id, 2),
                )
            # 編成内の保存値は、画面表示の1始まりキャラ番号に+1した値。
            slots[slot_index].cat_id = display_id + 1
            applied += 1
        save.lineups.selected_slot = lineup_index
        save.unlock_equip_menu()
        return [f"編成{lineup_index + 1}設定({applied}体・空枠{10 - applied})"]
    except Exception as e:
        print(f"[ERROR] lineup settings: {e}")
        return ["編成設定エラー"]


def apply_labyrinth_characters(save, settings):
    """地底迷宮の封印キャラを、最新キャラ数に追従しながら封印・解除する。"""
    if not settings:
        return []
    action = settings.get("action")
    if action not in LABYRINTH_CHARACTER_ACTIONS:
        return []

    trapped_names = ("trapped_cats", "sealed_cats", "unavailable_cats", "ushl3")
    active_names = ("active_cats", "current_cats", "surviving_cats", "ushl4")
    trapped = set(_labyrinth_value(save, trapped_names, []))
    active_order = list(dict.fromkeys(_labyrinth_value(save, active_names, [])))
    active = set(active_order)
    unlocked = _labyrinth_unlocked_cat_ids(save)
    selected = {
        display_id - 1 for display_id in settings.get("ids", [])
        if display_id >= 1 and display_id - 1 in unlocked
    }

    changed_ids = set()
    if action == "unlock_selected":
        changed_ids = trapped & selected
        trapped -= selected
    elif action == "unlock_all":
        changed_ids = set(trapped)
        trapped.clear()
    elif action == "seal_selected":
        changed_ids = selected - trapped
        trapped |= selected
        removed_active = active & selected
        if removed_active:
            active_order = [cat_id for cat_id in active_order if cat_id not in removed_active]
            active -= removed_active
            _remove_labyrinth_lineup_cats(save, removed_active)
    elif action == "seal_all":
        changed_ids = unlocked - trapped
        trapped = set(unlocked)
        _remove_labyrinth_lineup_cats(save, active)
        active_order = []
        active.clear()
    elif action == "release_lineup_all":
        changed_ids = set(active)
        _remove_labyrinth_lineup_cats(save, active)
        active_order = []
        active.clear()

    # 同じIDが封印中と現編成へ同時に入る状態は作らない。
    active_order = [cat_id for cat_id in active_order if cat_id not in trapped]
    active = set(active_order)
    trapped &= unlocked
    _set_labyrinth_value(save, trapped_names, sorted(trapped))
    _set_labyrinth_value(save, active_names, active_order)
    remaining = _sync_labyrinth_remaining(save, trapped, active)

    if hasattr(save, "ub25"):
        save.ub25 = True
    labels = {
        "unlock_selected": "指定封印解除",
        "unlock_all": "全封印解除",
        "seal_selected": "指定キャラ封印",
        "seal_all": "全キャラ封印",
        "release_lineup_all": "編成中キャラ全解除",
    }
    return [f"地底迷宮 {labels[action]}({len(changed_ids)}体・残り{remaining}体)"]


def apply_labyrinth_stages(save, maps):
    """選択された最深階までを連続クリアとして同期する。"""
    selected_floors = set()
    for map_id, stars in (maps or {}).items():
        if map_id != 0:
            continue
        for star, stages in stars.items():
            if star == 0:
                selected_floors.update(int(stage_id) for stage_id in stages)
    if not selected_floors:
        return []

    floor_order = _labyrinth_value(save, ("floor_order", "stage_order", "ushl2"), [])
    max_floors = len(floor_order) or 100
    requested = min(max_floors, max(selected_floors) + 1)
    current = int(_labyrinth_value(save, ("current_floor", "cleared_floor", "ush4"), 0) or 0)
    target = max(current, requested)

    stage_ids = list(getattr(save, "stage_ids_10s", []))
    known = set(stage_ids)
    for floor_index in range(target):
        stage_key = 33000000 + floor_index * 10
        if stage_key not in known:
            stage_ids.append(stage_key)
            known.add(stage_key)
    save.stage_ids_10s = stage_ids

    _set_labyrinth_value(save, ("current_floor", "cleared_floor", "ush4"), target)
    _set_labyrinth_value(save, ("highest_floor", "max_cleared_floor", "ush5"), target)
    _set_labyrinth_value(save, ("display_floor", "progress_floor", "ush7"), target)
    _set_labyrinth_value(save, ("remaining_floor_index", "uby10"), max(-128, min(127, max_floors - 1 - target)))
    if hasattr(save, "ui17"):
        save.ui17 = 33000
    if hasattr(save, "ub24"):
        save.ub24 = True
    if hasattr(save, "ub25"):
        save.ub25 = True
    remaining = _sync_labyrinth_remaining(save)
    return [f"地底迷宮 地底{target}層までクリア(残り{remaining}体)"]


def apply_event_stage_settings(save, selections):
    """イベント・塔・強襲・超獣などをステージ別の指定回数でクリアする。"""
    logs = []
    if selections is None:
        return logs
    labyrinth_characters = selections.get("_labyrinth_characters")
    for family_key, maps in selections.items():
        if family_key == "_labyrinth_characters":
            continue
        spec = EVENT_STAGE_FAMILIES.get(family_key)
        if not spec:
            continue
        if spec["kind"] == "labyrinth":
            logs.extend(apply_labyrinth_stages(save, maps))
            continue
        applied = 0
        for raw_map_id, stars in maps.items():
            try: map_id=int(raw_map_id)
            except (TypeError,ValueError): continue
            for raw_star, stages in stars.items():
                try: star=int(raw_star)
                except (TypeError,ValueError): continue
                for raw_stage_id, raw_clear_count in stages.items():
                    try: stage_id=int(raw_stage_id); clear_count=int(raw_clear_count)
                    except (TypeError,ValueError): continue
                    try:
                        if spec["kind"] == "event":
                            save.event_stages.clear_stage(
                                spec["group"], map_id, star, stage_id,
                                clear_amount=clear_count,
                            )
                        elif spec["kind"] == "tower":
                            save.tower.chapters.clear_stage(
                                map_id, star, stage_id, clear_count
                            )
                        elif spec["kind"] == "catamin_stages":
                            chapters = save.catamin_stages.chapters
                            _ensure_standard_chapter_map(chapters, map_id)
                            chapters.clear_stage(
                                map_id, star, stage_id, clear_count
                            )
                            # ネコビタンステージは通常のステージ別回数に加えて、
                            # マップ単位の表示回数も別dictへ保存される。
                            completion_key = spec["base_index"] + map_id
                            save.event_stages.chapter_completion_count[completion_key] = max(
                                clear_count,
                                save.event_stages.chapter_completion_count.get(completion_key, 0),
                            )
                        elif spec["kind"] == "dojo_chapters":
                            save.dojo_chapters.create(map_id)
                            chapter = save.dojo_chapters.chapters[map_id].chapters[star]
                            chapter.clear_progress = max(chapter.clear_progress, stage_id + 1)
                            chapter.stages[stage_id].clear_times = clear_count
                            chapter.unlock_state = 3
                        else:
                            container = getattr(save, spec["kind"])
                            _ensure_gauntlet_map(container, map_id)
                            container.clear_stage(map_id, star, stage_id, clear_count)
                        applied += 1
                    except (AttributeError, IndexError, TypeError) as e:
                        print(f"[ERROR] event_stage_settings[{family_key}][{map_id}][{star}][{stage_id}]: {e}")
        if applied:
            logs.append(f"{spec['label']}({applied}ステージ)")
    logs.extend(apply_labyrinth_characters(save, labyrinth_characters))
    return logs


def apply_special_stages(save, selections):
    """選択されたゾンビ襲来・魔界編ステージだけをクリアする。"""
    logs = []
    if selections is None:
        return logs

    if "zombie" in selections:
        applied = 0
        zombie = selections.get("zombie", {})
        for position, stage_ids in zombie.items():
            if not 0 <= position < len(MAIN_STORY_REAL_INDEX):
                continue
            chapter_key = MAIN_STORY_REAL_INDEX[position]
            if chapter_key not in save.outbreaks.chapters:
                save.outbreaks.chapters[chapter_key] = ZombieChapter(chapter_key, {})
            chapter = save.outbreaks.chapters[chapter_key]
            current_chapter = save.outbreaks.current_outbreaks.get(chapter_key)
            for stage_id in stage_ids:
                chapter.outbreaks[stage_id] = ZombieOutbreak(True)
                if current_chapter is not None:
                    current_chapter.outbreaks.pop(stage_id, None)
                applied += 1
            if current_chapter is not None and not current_chapter.outbreaks:
                save.outbreaks.current_outbreaks.pop(chapter_key, None)
        if applied:
            logs.append(f"ゾンビ({applied}ステージ)")

    if "aku" in selections:
        applied_ids = set()
        stage_ids = selections.get("aku", [])
        if hasattr(save, "aku") and save.aku and save.aku.chapters:
            for chapters_stars in save.aku.chapters:
                for chapter in chapters_stars.chapters:
                    valid_ids = [stage_id for stage_id in stage_ids if stage_id < len(chapter.stages)]
                    for stage_id in valid_ids:
                        chapter.stages[stage_id].clear_times = 1
                        applied_ids.add(stage_id)
                    if valid_ids:
                        chapter.current_stage = max(chapter.current_stage, max(valid_ids))
        if applied_ids:
            logs.append(f"魔界編({len(applied_ids)}ステージ)")
    if "aku_ex" in selections and 0 in selections.get("aku_ex", []):
        _sync_jagando_clear(save)
        logs.append("富士山EX(破壊神ジャガンドー)")
    return logs


def apply_ototo_settings(save, ototo_settings):
    """個別指定された城だけを更新する。part 0はセーブ上だけ0始まり。"""
    if not ototo_settings:
        return []
    applied = []
    name_by_id = {
        int(item["id"]): item.get("name", f"城強化 #{item['id']}")
        for item in get_ototo_metadata().get("cannons", [])
    }
    for raw_cannon_id, setting in ototo_settings.items():
        try:
            cannon_id = int(raw_cannon_id)
            cannon = save.ototo.cannons.cannons.get(cannon_id)
            if cannon is None:
                cannon = core.game.gamoto.ototo.Cannon(0, [])
                save.ototo.cannons.cannons[cannon_id] = cannon
            required_size = 1 if cannon_id == 0 else 3
            levels = list(cannon.levels)
            while len(levels) < required_size:
                levels.append(0)
            changed_parts = []
            for raw_part_id, raw_level in setting.get("levels", {}).items():
                part_id = int(raw_part_id)
                display_level = int(raw_level)
                if not (0 <= part_id < required_size):
                    continue
                levels[part_id] = display_level - 1 if part_id == 0 else display_level
                changed_parts.append(display_level)
            if not changed_parts:
                continue
            cannon.levels = levels[:required_size]
            if cannon_id != 0:
                cannon.development = 3
            applied.append(f"{name_by_id.get(cannon_id, f'城強化 #{cannon_id}')}個別設定")
        except Exception as e:
            print(f"[ERROR] ototo detail {raw_cannon_id}: {e}")
    return applied


def apply_daiko_segment(save, selected_items: list, char_list: list, custom_amounts: dict, custom_playtime: str = "", main_story_chapters=None, character_settings=None) -> list:
    applied_logs = []
    save.show_ban_message = False

    def amt(key):
        return int(custom_amounts.get(key, 0))

    if "custom_catfood" in selected_items:
        _sv(save, "catfood", amt("custom_catfood")); applied_logs.append(f"猫缶({amt('custom_catfood')})")

    if "custom_xp" in selected_items:
        _sv(save, "xp", amt("custom_xp")); applied_logs.append(f"XP({amt('custom_xp')})")

    if "custom_np" in selected_items:
        _sv(save, "np", amt("custom_np")); applied_logs.append(f"NP({amt('custom_np')})")

    if "custom_normal_tickets" in selected_items:
        _sv(save, "normal_tickets", amt("custom_normal_tickets")); applied_logs.append(f"銀チケ({amt('custom_normal_tickets')})")

    if "custom_rare_tickets" in selected_items:
        _sv(save, "rare_tickets", amt("custom_rare_tickets")); applied_logs.append(f"金チケ({amt('custom_rare_tickets')})")

    if "custom_platinum_tickets" in selected_items:
        _sv(save, "platinum_tickets", amt("custom_platinum_tickets")); applied_logs.append(f"プラチナ({amt('custom_platinum_tickets')})")

    if "custom_legend_tickets" in selected_items:
        _sv(save, "legend_tickets", amt("custom_legend_tickets")); applied_logs.append(f"レジェンドチケ({amt('custom_legend_tickets')})")

    if "custom_leadership" in selected_items:
        _sv(save, "leadership", amt("custom_leadership")); applied_logs.append(f"リーダーシップ({amt('custom_leadership')})")

    if "custom_catseyes" in selected_items:
        try: _sv_list(save, "catseyes", amt("custom_catseyes")); applied_logs.append(f"キャッツアイ({amt('custom_catseyes')})")
        except Exception as e: print(f"[ERROR] custom_catseyes: {e}")

    if "custom_catamins" in selected_items:
        try: _sv_list(save, "catamins", amt("custom_catamins")); applied_logs.append(f"ネコビタン({amt('custom_catamins')})")
        except Exception as e: print(f"[ERROR] custom_catamins: {e}")

    if "custom_base_materials" in selected_items:
        try:
            if hasattr(save, 'ototo') and hasattr(save.ototo, 'base_materials'):
                for material in save.ototo.base_materials.materials:
                    try: material.amount = amt("custom_base_materials")
                    except Exception:
                        try: material.amount.value = amt("custom_base_materials")
                        except Exception: pass
                applied_logs.append(f"城素材({amt('custom_base_materials')})")
        except Exception as e: print(f"[ERROR] custom_base_materials: {e}")

    if "custom_matatabi" in selected_items:
        try: _sv_list(save, "catfruit", amt("custom_matatabi")); applied_logs.append(f"マタタビ({amt('custom_matatabi')})")
        except Exception as e: print(f"[ERROR] custom_matatabi: {e}")

    if "custom_talent_orbs" in selected_items:
        try:
            orb_ids = _latest_talent_orb_ids()
            for orb_id in orb_ids:
                save.talent_orbs.set_orb(orb_id, amt("custom_talent_orbs"))
            applied_logs.append(f"本能玉({len(orb_ids)}種類・{amt('custom_talent_orbs')})")
        except Exception as e: print(f"[ERROR] custom_talent_orbs: {e}")

    if "custom_battle_items" in selected_items:
        try:
            for b_item in save.battle_items.items:
                try: b_item.amount = amt("custom_battle_items")
                except Exception:
                    try: b_item.amount.value = amt("custom_battle_items")
                    except Exception: pass
            applied_logs.append(f"バトルアイテム({amt('custom_battle_items')})")
        except Exception as e: print(f"[ERROR] custom_battle_items: {e}")

    if "main_story_clear" in selected_items:
        try:
            chapters = save.story.chapters
            if main_story_chapters is None:
                target_indices = list(range(len(chapters)))
                selected_positions = list(range(len(MAIN_STORY_CHAPTER_LABELS)))
            else:
                selected_positions = [p for p in main_story_chapters if p < len(MAIN_STORY_REAL_INDEX)]
                target_indices = [MAIN_STORY_REAL_INDEX[p] for p in selected_positions if MAIN_STORY_REAL_INDEX[p] < len(chapters)]
            for idx in target_indices:
                chapter = chapters[idx]
                chapter.clear_chapter()
                for i in range(len(chapter.stages)):
                    if i < 48: chapter.stages[i].treasure = 3
            if main_story_chapters is None or len(selected_positions) == len(MAIN_STORY_CHAPTER_LABELS):
                applied_logs.append("メインクリア")
            else:
                names = [MAIN_STORY_CHAPTER_LABELS[p] for p in selected_positions if p < len(MAIN_STORY_CHAPTER_LABELS)]
                applied_logs.append(f"メインクリア({'/'.join(names)})")
        except Exception as e: print(f"[ERROR] main_story_clear: {e}")

    if "zombie_clear" in selected_items:
        try:
            for chapter_key in [0, 1, 2, 4, 5, 6, 7, 8, 9]:
                if chapter_key not in save.outbreaks.chapters:
                    save.outbreaks.chapters[chapter_key] = ZombieChapter(chapter_key, {})
                chapter = save.outbreaks.chapters[chapter_key]
                for stage_id in range(48):
                    chapter.outbreaks[stage_id] = ZombieOutbreak(True)
            save.outbreaks.current_outbreaks = {}
            applied_logs.append("ゾンビ")
        except Exception as e:
            print(f"[ERROR] zombie_clear: {e}")

    if "aku_clear" in selected_items:
        try:
            if hasattr(save, 'aku') and save.aku and save.aku.chapters:
                for chapters_stars in save.aku.chapters:
                    for chapter in chapters_stars.chapters:
                        if chapter.stages and len(chapter.stages) > 0:
                            chapter.current_stage = len(chapter.stages) - 1
                            for stage in chapter.stages:
                                stage.clear_times = 1
                _sync_jagando_clear(save)
            applied_logs.append("魔界編")
        except Exception as e: print(f"[ERROR] aku_clear: {e}")

    if "legend_clear" in selected_items:
        try: applied_logs.extend(apply_legend_stages(save, full_legend_selection("legend")))
        except Exception as e: print(f"[ERROR] legend_clear: {e}")

    if "true_legend_clear" in selected_items:
        try:
            applied_logs.extend(apply_legend_stages(save, full_legend_selection("true_legend")))
        except Exception as e: print(f"[ERROR] true_legend_clear: {e}")

    if "zero_legend_clear" in selected_items:
        try:
            applied_logs.extend(apply_legend_stages(save, full_legend_selection("zero_legend")))
        except Exception as e: print(f"[ERROR] zero_legend_clear: {e}")

    if "event_clear" in selected_items:
        try:
            for group_id in range(len(save.event_stages.chapters)): save.event_stages.clear_group(group_id)
            applied_logs.append("イベント")
        except Exception as e: print(f"[ERROR] event_clear: {e}")

    if "gamatoto_max" in selected_items:
        try:
            g_levels = core.core_data.get_gamatoto_levels(save)
            save.gamatoto.xp = g_levels.get_xp_from_level(g_levels.get_max_level())
            applied_logs.append("ガマトト")
        except Exception as e: print(f"[ERROR] gamatoto_max: {e}")

    if "gamatoto_helpers" in selected_items:
        try:
            new_helpers = []
            for i in range(129, 139): new_helpers.append(core.game.gamoto.gamatoto.Helper(i))
            save.gamatoto.helpers.helpers = new_helpers
            applied_logs.append("助手")
        except Exception as e: print(f"[ERROR] gamatoto_helpers: {e}")

    if "ototo_max" in selected_items:
        try:
            for cannon_id, cannon in save.ototo.cannons.cannons.items():
                cannon.development = 3
                if cannon_id == 0: cannon.levels = [29]
                else: cannon.levels = [29, 20, 20]
            applied_logs.append("オトート")
        except Exception as e: print(f"[ERROR] ototo_max: {e}")

    if "cat_shrine_max" in selected_items:
        try:
            save.cat_shrine.xp_offering = 100000000
            applied_logs.append("神社")
        except Exception as e: print(f"[ERROR] cat_shrine_max: {e}")

    if "gold_membership" in selected_items:
        try:
            save.officer_pass.gold_pass.get_gold_pass(114514, 365, save)
            applied_logs.append("ゴールド")
        except Exception as e: print(f"[ERROR] gold_membership: {e}")

    if "slots_max" in selected_items:
        try: save.lineups.unlocked_slots = 19; applied_logs.append("スロット")
        except Exception as e: print(f"[ERROR] slots_max: {e}")

    if "medals_all" in selected_items:
        try:
            medal_names = core.core_data.get_medal_names(save)
            if medal_names.medal_names:
                for i in range(len(medal_names.medal_names)): save.medals.add_medal(i)
            applied_logs.append("メダル")
        except Exception as e: print(f"[ERROR] medals_all: {e}")

    if "skip_tutorial" in selected_items:
        try: save.story.clear_tutorial(save); applied_logs.append("チュートリアル")
        except Exception as e: print(f"[ERROR] skip_tutorial: {e}")

    if "hide_rank_up" in selected_items:
        try:
            save.unlock_popups_11 = [1] * 3
            if hasattr(save, 'max_rank_up_sale'): save.max_rank_up_sale()
            else: save.rank_up_sale_value = 0x7FFFFFFF
            user_rank = save.calculate_user_rank()
            rank_gifts = save.user_rank_rewards.read_rank_gifts(save)
            if rank_gifts and rank_gifts.rank_gift:
                for rank_gift in rank_gifts.rank_gift:
                    if rank_gift.threshold <= user_rank:
                        save.user_rank_rewards.set_claimed(rank_gift.index, False)
            applied_logs.append("ポップアップ非表示")
        except Exception as e: print(f"[ERROR] hide_rank_up: {e}")

    if "user_rank_rewards_claimed" in selected_items:
        try:
            changed, eligible = _set_all_user_rank_rewards(save, True)
            applied_logs.append(f"UR報酬全受取({eligible}件・変更{changed}件)")
        except Exception as e:
            print(f"[ERROR] user_rank_rewards_claimed: {e}")

    if "user_rank_rewards_unclaimed" in selected_items:
        try:
            changed, eligible = _set_all_user_rank_rewards(save, False)
            applied_logs.append(f"UR報酬全未受取(変更{changed}件)")
        except Exception as e:
            print(f"[ERROR] user_rank_rewards_unclaimed: {e}")

    if "catguide_rewards_claimed" in selected_items:
        try:
            changed, targets = _set_all_catguide_rewards(save, True)
            applied_logs.append(f"猫図鑑報酬全受取({targets}体・変更{changed}体)")
        except Exception as e:
            print(f"[ERROR] catguide_rewards_claimed: {e}")

    if "catguide_rewards_unclaimed" in selected_items:
        try:
            changed, targets = _set_all_catguide_rewards(save, False)
            applied_logs.append(f"猫図鑑報酬全未受取(変更{changed}体)")
        except Exception as e:
            print(f"[ERROR] catguide_rewards_unclaimed: {e}")

    if "cat_scratcher_reset" in selected_items:
        try:
            # 実機の未実施データでも開催日(start_times)は残る。
            # BCSFE reset()はそれまで消すため、結果と完了フラグだけ戻す。
            save.cat_scratcher.completed = {}
            save.cat_scratcher.values = {}
            applied_logs.append("スクラッチ未実施化")
        except Exception as e:
            print(f"[ERROR] cat_scratcher_reset: {e}")

    if "unlock_enemy_guide" in selected_items:
        try:
            enemy_dict = core.game.battle.enemy.EnemyDictionary(save)
            valid_enemies = enemy_dict.get_valid_enemies()
            if valid_enemies:
                for enemy_id in valid_enemies:
                    save.enemy_guide[enemy_id] = 1
                applied_logs.append("敵図鑑全解放")
        except Exception as e: print(f"[ERROR] unlock_enemy_guide: {e}")

    if "add_playtime_720h" in selected_items:
        try:
            current_play_time = PlayTime(save.officer_pass.play_time)
            added_time = PlayTime.from_hours(720)
            new_play_time = current_play_time + added_time
            save.officer_pass.play_time = new_play_time.frames
            applied_logs.append("プレイ時間+720h")
        except Exception as e: print(f"[ERROR] add_playtime_720h: {e}")
    elif "custom_playtime" in selected_items:
        try:
            parsed = validate_playtime_str(str(custom_playtime))
            if parsed:
                hours, minutes = parsed
                save.officer_pass.play_time = PlayTime.from_hours_mins_secs(hours, minutes, 0).frames
                applied_logs.append(f"プレイ時間({hours}:{minutes:02d})")
            else:
                print("[ERROR] custom_playtime: 不正な形式のためスキップ")
        except Exception as e: print(f"[ERROR] custom_playtime: {e}")

    if "all_missions_clear" in selected_items:
        try:
            completed = _complete_all_defined_missions(save)
            applied_logs.append(f"全ミッションクリア({completed}件・全種類)")
        except Exception as e:
            print(f"[ERROR] all_missions_clear: {e}")
            traceback.print_exc()

    if "base_upgrades_max" in selected_items:
        try:
            for i in range(len(save.special_skills.skills)):
                if i == 2: save.special_skills.skills[i].upgrade.base = 9; save.special_skills.skills[i].upgrade.plus = 0
                else: save.special_skills.skills[i].upgrade.base = 19; save.special_skills.skills[i].upgrade.plus = 10
            applied_logs.append("全施設Max")
        except Exception as e: print(f"[ERROR] base_upgrades_max: {e}")
    elif "custom_base_upgrades" in selected_items:
        try:
            v = amt("custom_base_upgrades")
            for i in range(len(save.special_skills.skills)):
                if i == 2:
                    save.special_skills.skills[i].upgrade.base = max(v - 1, 0)
                    save.special_skills.skills[i].upgrade.plus = 0
                else:
                    base_level = min(max(v - 1, 0), 19)
                    plus_level = max(v - (base_level + 1), 0)
                    save.special_skills.skills[i].upgrade.base = base_level
                    save.special_skills.skills[i].upgrade.plus = plus_level
            applied_logs.append(f"全施設({v})")
        except Exception as e: print(f"[ERROR] custom_base_upgrades: {e}")

    if "unlock_all_cats" in selected_items:
        try:
            for cat in save.cats.cats: cat.unlock(save)
            applied_logs.append("全解放")
        except Exception as e: print(f"[ERROR] unlock_all_cats: {e}")

    if char_list:
        char_applied = []
        for char_val in char_list:
            try:
                cat_id = int(char_val) - 1
                cat = save.cats.get_cat_by_id(cat_id)
                if not cat: continue
                if "unlock_specific" in selected_items: cat.unlock(save); char_applied.append(f"解放({char_val})")
                if "remove_specific" in selected_items: cat.remove(reset=True, save_file=save); char_applied.append(f"削除({char_val})")
            except: pass
        if char_applied: applied_logs.extend(char_applied)

    # 名前選択UIの指定キャラ。従来の1始まりID入力とは独立して併用できる。
    if character_settings:
        char_applied = []
        form_counts = _character_form_counts()
        true_form_states = _character_true_form_states()
        talent_definitions = _talent_definitions_by_cat() if "talents_specific" in selected_items else {}
        for setting in character_settings:
            try:
                display_id = int(setting["id"])
                cat = save.cats.get_cat_by_id(display_id - 1)
                if not cat:
                    continue
                if "unlock_specific" in selected_items:
                    cat.unlock(save)
                    char_applied.append(f"解放({display_id})")
                if "remove_specific" in selected_items:
                    cat.remove(reset=True, save_file=save)
                    char_applied.append(f"削除({display_id})")
                    continue
                if "level_specific" in selected_items:
                    cat.unlock(save)
                    if setting.get("level_mode") == "random":
                        base_min = int(setting.get("base_level_min", 1))
                        base_max = int(setting.get("base_level_max", 60))
                        plus_min = int(setting.get("plus_level_min", 0))
                        plus_max = int(setting.get("plus_level_max", 90))
                        base_level = base_min + secrets.randbelow(base_max - base_min + 1)
                        plus_level = plus_min + secrets.randbelow(plus_max - plus_min + 1)
                    else:
                        base_level = int(setting["base_level"])
                        plus_level = int(setting["plus_level"])
                    cat.upgrade.base = max(0, base_level - 1)
                    cat.upgrade.plus = max(0, plus_level)
                    char_applied.append(
                        f"Lv.{base_level}+{plus_level}({display_id})"
                    )
                if "form_specific" in selected_items:
                    form = _set_cat_form(
                        save,
                        cat,
                        form_counts.get(display_id, 1),
                        int(setting["form"]),
                        true_form_states.get(display_id, 2),
                    )
                    char_applied.append(f"第{form}形態({display_id})")
                if "max_specific" in selected_items:
                    cat.unlock(save)
                    cat.upgrade.base = 59
                    cat.upgrade.plus = 90
                    char_applied.append(f"Lv.Max+({display_id})")
                if "max_specific_2" in selected_items:
                    cat.unlock(save)
                    cat.upgrade.base = 59
                    char_applied.append(f"Lv.Max({display_id})")
                if "true_form_specific" in selected_items:
                    form = _set_cat_latest_form(save, cat, form_counts, true_form_states)
                    if form is None:
                        char_applied.append(f"最終形態スキップ・形態定義未取得({display_id})")
                    else:
                        char_applied.append(f"最終形態・第{form}形態({display_id})")
                if "talents_specific" in selected_items:
                    if not cat.unlocked:
                        char_applied.append(f"本能スキップ・未解放({display_id})")
                    else:
                        applied = _apply_character_talents(
                            cat, display_id, setting, talent_definitions
                        )
                        if applied:
                            action_label = {
                                "set": "本能設定",
                                "disable_selected": "選択本能無効",
                                "disable_all": "全本能無効",
                            }.get(setting.get("talent_action"), "本能設定")
                            char_applied.append(f"{action_label}({display_id}: {applied}個)")
            except Exception as e:
                print(f"[ERROR] character_settings: {e}")
        if char_applied:
            applied_logs.extend(char_applied)

    if "max_all_cats_plus" in selected_items:
        try:
            for cat in save.cats.cats:
                if cat.unlocked:
                    cat.upgrade.base = 59; cat.upgrade.plus = 90
            applied_logs.append("全Lv.Max+")
        except Exception as e: print(f"[ERROR] max_all_cats_plus: {e}")

    if "max_all_cats" in selected_items:
        try:
            for cat in save.cats.cats:
                if cat.unlocked:
                    cat.upgrade.base = 59
            applied_logs.append("全Lv.Max")
        except Exception as e: print(f"[ERROR] max_all_cats: {e}")

    if "true_form_all" in selected_items:
        try:
            unlocked_cats = [cat for cat in save.cats.cats if cat.unlocked]
            form_counts = _character_form_counts()
            true_form_states = _character_true_form_states()
            for cat in unlocked_cats:
                _set_cat_latest_form(save, cat, form_counts, true_form_states)
            skipped = sum(1 for cat in unlocked_cats if cat.id + 1 not in form_counts)
            applied_logs.append(
                f"全最大形態(形態定義未取得{skipped}体を除外)" if skipped else "全最大形態"
            )
        except Exception as e: print(f"[ERROR] true_form_all: {e}")

    if "talents_all" in selected_items:
        try:
            talent_data = core.TalentData.from_game_data(save)
            if talent_data:
                for cat in save.cats.cats:
                    if not cat.unlocked: continue
                    cat_skill = talent_data.get_cat_skill(cat.id)
                    if cat_skill:
                        if cat.talents is None:
                            cat.talents = []
                        for skill in cat_skill.skills:
                            if skill.ability_id <= 0 or skill.text_id <= 0:
                                continue
                            max_lv = skill.max_lv if skill.max_lv != 0 else 1
                            existing_talent = next(
                                (t for t in cat.talents if t.id == skill.ability_id), None
                            )
                            if existing_talent:
                                existing_talent.level = max_lv
                            else:
                                cat.talents.append(Talent(skill.ability_id, max_lv))
                applied_logs.append("全本能")
            else:
                applied_logs.append("エラー: 本能データロード失敗")
        except Exception as e:
            print(f"[ERROR] talents_all: {e}")

    if "talents_disable_all" in selected_items:
        try:
            disabled = 0
            for cat in save.cats.cats:
                if cat.talents is None:
                    continue
                for talent in cat.talents:
                    if talent.level:
                        talent.level = 0
                        disabled += 1
            applied_logs.append(f"全キャラ本能無効({disabled}個)")
        except Exception as e:
            print(f"[ERROR] talents_disable_all: {e}")

    if char_list:
        char_applied = []
        for char_val in char_list:
            try:
                cat_id = int(char_val) - 1
                cat = save.cats.get_cat_by_id(cat_id)
                if not cat or not cat.unlocked: continue
                if "max_specific" in selected_items: cat.upgrade.base = 59; cat.upgrade.plus = 90; char_applied.append(f"Lv.Max+({char_val})")
                if "max_specific_2" in selected_items: cat.upgrade.base = 59; char_applied.append(f"Lv.Max({char_val})")
                if "true_form_specific" in selected_items:
                    form = _set_cat_latest_form(save, cat)
                    if form is None:
                        char_applied.append(f"最終形態スキップ・形態定義未取得({char_val})")
                    else:
                        char_applied.append(f"最終形態・第{form}形態({char_val})")
            except: pass
        if char_applied: applied_logs.extend(char_applied)

    if "remove_error_cats" in selected_items:
        try:
            removed_count = 0
            for err_id in ERROR_CAT_IDS:
                cat = save.cats.get_cat_by_id(err_id - 1)
                if cat: cat.remove(reset=True, save_file=save); removed_count += 1
            if removed_count > 0:
                applied_logs.append(f"エラーキャラ削除({removed_count}体)")
        except Exception as e: print(f"[ERROR] remove_error_cats: {e}")

    return applied_logs


def _apply_all_segments_unlocked(save_file, selected, char_list, custom_amounts, custom_playtime="", main_story_chapters=None, vip_items=None, legend_stages=None, vip_facilities=None, vip_talent_orbs=None, special_stages=None, character_settings=None, main_story_stages=None, event_stage_settings=None, lineup_settings=None, ototo_settings=None, dojo_score_settings=None, future_score_settings=None):
    final_logs = apply_vip_items(save_file, vip_items)
    final_logs.extend(apply_legend_stages(save_file, legend_stages))
    final_logs.extend(apply_vip_facilities(save_file, vip_facilities))
    final_logs.extend(apply_vip_talent_orbs(save_file, vip_talent_orbs))
    final_logs.extend(apply_special_stages(save_file, special_stages))
    final_logs.extend(apply_main_story_stages(save_file, main_story_stages))
    final_logs.extend(apply_event_stage_settings(save_file, event_stage_settings))
    final_logs.extend(apply_lineup_settings(save_file, lineup_settings))
    final_logs.extend(apply_ototo_settings(save_file, ototo_settings))
    final_logs.extend(apply_dojo_score_settings(save_file, dojo_score_settings))
    final_logs.extend(apply_future_score_settings(save_file, future_score_settings))
    s1 = selected.get("s1", [])
    s2 = selected.get("s2", [])
    s3 = selected.get("s3", [])
    s4 = selected.get("s4", [])
    for i, segment in enumerate([s1, s2, s3, s4], 1):
        if not segment and (i != 3 or not char_list): continue
        items = []
        for item in segment:
            if item == "all_stage_clear":
                items.extend(["main_story_clear", "zombie_clear", "aku_clear",
                               "legend_clear", "true_legend_clear", "zero_legend_clear", "event_clear"])
            else:
                items.append(item)
        # VIP個別指定がある親項目は、従来の「全配列を一括更新」処理から除外する。
        if vip_items:
            granular_values = set().union(*(
                VIP_ITEM_SELECTED_VALUES.get(group_key, set()) for group_key in vip_items
            ))
            items = [item for item in items if item not in granular_values]
        # 詳細選択が送られたシリーズは従来の全クリア処理を抑止する。
        if legend_stages is not None:
            granular_legend_values = {
                LEGEND_SELECTED_VALUES[key] for key in legend_stages if key in LEGEND_SELECTED_VALUES
            }
            items = [item for item in items if item not in granular_legend_values]
        if special_stages is not None:
            granular_special_values = {
                "zombie": "zombie_clear", "aku": "aku_clear", "aku_ex": "aku_clear"
            }
            suppressed = {granular_special_values[key] for key in special_stages if key in granular_special_values}
            items = [item for item in items if item not in suppressed]
        if main_story_stages is not None:
            items = [item for item in items if item != "main_story_clear"]
        if event_stage_settings is not None:
            items = [item for item in items if item != "event_clear"]
        if vip_facilities is not None:
            items = [item for item in items if item not in {"base_upgrades_max", "custom_base_upgrades"}]
        if vip_talent_orbs is not None:
            items = [item for item in items if item not in {"talent_orbs", "custom_talent_orbs"}]
        if ototo_settings is not None:
            items = [item for item in items if item not in {"ototo_max", "ototo_detailed"}]
        final_logs.extend(apply_daiko_segment(
            save_file,
            list(dict.fromkeys(items)),
            char_list if i == 3 else [],
            custom_amounts,
            custom_playtime,
            main_story_chapters,
            character_settings if i == 3 else None,
        ))
    # 形態を扱う操作時だけ既存の不可能な状態も修復する。通常のアイテム・
    # ステージ操作で、配布metadataより新しい実機形態を触らないための制限。
    form_actions = {"form_specific", "true_form_specific", "true_form_all"}
    should_repair_forms = any(form_actions.intersection(segment) for segment in (s1, s2, s3, s4))
    if should_repair_forms or lineup_settings is not None:
        repaired_forms = _normalise_cat_form_flags(save_file)
        if repaired_forms:
            final_logs.append(f"形態・進化権自動修正({repaired_forms}体)")
    return final_logs


def _apply_all_segments(save_file, selected, char_list, custom_amounts, custom_playtime="", main_story_chapters=None, vip_items=None, legend_stages=None, vip_facilities=None, vip_talent_orbs=None, special_stages=None, character_settings=None, main_story_stages=None, event_stage_settings=None, lineup_settings=None, ototo_settings=None, dojo_score_settings=None, future_score_settings=None):
    """BCSFEのsave依存グローバルキャッシュを別ジョブと混在させず適用する。"""
    with BCSFE_EDIT_LOCK:
        ensure_latest_save_schema(save_file)
        # BCSFE 3.6.0はgetterやchara_drop等をプロセス全体でキャッシュする。
        # すべて同じ最新版へ固定し、saveを保持する派生キャッシュはジョブごとに破棄する。
        core.core_data.game_data_getter = _latest_jp_game_data_getter()
        for cache_name in (
            "gatya_item_names", "gatya_item_buy", "chara_drop", "gamatoto_levels",
            "gamatoto_members_name", "localizable", "abilty_data", "enemy_names",
            "rank_gift_descriptions", "rank_gifts", "treasure_text", "cat_shrine_levels",
            "medal_names", "mission_names", "mission_conditions",
        ):
            if hasattr(core.core_data, cache_name):
                setattr(core.core_data, cache_name, None)
        return _apply_all_segments_unlocked(
            save_file, selected, char_list, custom_amounts, custom_playtime,
            main_story_chapters, vip_items, legend_stages, vip_facilities,
            vip_talent_orbs, special_stages, character_settings,
            main_story_stages, event_stage_settings, lineup_settings, ototo_settings,
            dojo_score_settings, future_score_settings,
        )


def run_job_daiko(job_id, operation_id, transfer_code, auth_code, selected, char_list, custom_amounts, custom_playtime="", main_story_chapters=None, vip_items=None, legend_stages=None, vip_facilities=None, vip_talent_orbs=None, special_stages=None, character_settings=None, main_story_stages=None, event_stage_settings=None, lineup_settings=None, ototo_settings=None, dojo_score_settings=None, future_score_settings=None, access_tier="free"):
    def update(d):
        d["updated_at"] = time.time()
        _update_job(job_id, d)
    handler = None
    checkpoint_codes = None
    final_issue_started = False
    try:
        update({"status": "running", "started_at": time.time(), "log": "サーバーに接続中..."})
        _update_operation(operation_id, status="running", error=None)

        cc = core.CountryCode.from_code("jp")
        gv = core.GameVersion(TARGET_GAME_VERSION_NUMBER)

        char_list = [c.strip() for c in char_list if str(c).strip().isdigit()]

        handler, result = ServerHandler.from_codes(
            transfer_code, auth_code, cc, gv, save_backup=False
        )
        if handler is None:
            update({"status": "error", "error": "エラー: コード無効。"})
            _close_operation(
                operation_id,
                status="error",
                recovery_status="not_available",
                error="コード無効のため、セーブデータは取得されていません。",
            )
            return

        update({
            "transfer_received": True,
            "log": "引き継ぎ取得済み・復旧用コードを保存中...",
        })
        _save_operation_snapshot(operation_id, handler.save_file)

        # 入力コードはfrom_codes成功時点で消費される。編集・保存中に
        # プロセスが落ちてもアカウントを回収できるよう、変更前データで
        # 復旧用コードを先に発行し、SQLiteのジョブ記録へ即時保存する。
        checkpoint_codes = handler.get_codes(tries=2)
        if not checkpoint_codes:
            update({
                "status": "error",
                "transfer_received": True,
                "admin_recovery_required": True,
                "error": (
                    "引き継ぎ取得後、作業前の復旧用コードを発行できませんでした。"
                    "同じ操作を再実行せず管理者へ連絡してください。"
                ),
            })
            _update_operation(
                operation_id, status="error",
                error="引き継ぎ取得後、作業前の復旧用コードを発行できませんでした。",
                recovery_status="reissue_failed",
            )
            return
        update({
            "recovery_transfer_code": checkpoint_codes[0],
            "recovery_auth_code": checkpoint_codes[1],
            "admin_recovery_required": False,
            "log": "復旧用コード保存済み・データを適用中...",
        })

        final_logs = _apply_all_segments(handler.save_file, selected, char_list, custom_amounts, custom_playtime, main_story_chapters, vip_items, legend_stages, vip_facilities, vip_talent_orbs, special_stages, character_settings, main_story_stages, event_stage_settings, lineup_settings, ototo_settings, dojo_score_settings, future_score_settings)
        # 最終発行だけ失敗した時は、編集済みデータから管理者が再発行できるよう更新。
        _save_operation_snapshot(operation_id, handler.save_file)

        update({"log": "サーバーに保存中..."})
        final_issue_started = True
        codes = handler.get_codes()
        if codes:
            t, a = codes
            total_count = increment_usage_count()
            update({
                "status": "done", "transfer_code": t, "auth_code": a,
                "applied": final_logs, "recovery_transfer_code": None,
                "recovery_auth_code": None, "admin_recovery_required": False,
            })
            _close_operation(
                operation_id, status="done", recovery_status="not_needed"
            )
            send_usage_log(access_tier, final_logs, total_count, USAGE_DB_PATH)
        else:
            # 最終POSTはサーバー側だけ成功して応答が失われた可能性がある。
            # 直後に自動再発行すると既知のコードまで無効化し得るため、最新の
            # 編集済みスナップショットを残して管理パネルから再発行する。
            error_text = (
                "引き継ぎ取得後の保存通信を確認できませんでした。"
                "同じ操作を再実行せず、管理パネルから引き継ぎコードを再発行してください。"
            )
            update({
                "status": "error",
                "error": error_text,
                "transfer_received": True,
                "admin_recovery_required": True,
            })
            _update_operation(
                operation_id,
                status="error",
                error=error_text,
                recovery_status="reissue_failed",
            )

    except Exception as e:
        payload = {"status": "error", "error": _safe_error_message(e)}
        # 最終発行を始める前ならチェックポイントコードは確実に既知。
        # 発行開始後は応答喪失の可能性があるため、再送せずsnapshotを残す。
        if checkpoint_codes and not final_issue_started:
            payload.update({
                "recovery_transfer_code": checkpoint_codes[0],
                "recovery_auth_code": checkpoint_codes[1],
                "admin_recovery_required": False,
                "error": "処理中にエラーが発生しました。引き継ぎコードを確認してください。",
            })
        elif handler is not None:
            payload.update({
                "transfer_received": True,
                "admin_recovery_required": True,
                "error": (
                    "引き継ぎ取得後にエラーが発生しました。"
                    "同じ操作を再実行せず、管理パネルから引き継ぎコードを再発行してください。"
                ),
            })
        if checkpoint_codes and not final_issue_started:
            payload["admin_recovery_required"] = False
            _close_operation(
                operation_id,
                status="error",
                recovery_status="client_code_issued",
                error=payload["error"],
                issued_codes=checkpoint_codes,
            )
        elif handler is None:
            payload["admin_recovery_required"] = False
            _close_operation(
                operation_id,
                status="error",
                recovery_status="not_available",
                error=payload["error"],
            )
        else:
            payload["admin_recovery_required"] = True
            _update_operation(
                operation_id, status="error", error=payload["error"],
                recovery_status="reissue_failed",
            )
        update(payload)
        print(traceback.format_exc())


def run_job_create(job_id, selected, char_list, custom_amounts, count=1, custom_playtime="", account_type_key="new", main_story_chapters=None, vip_items=None, legend_stages=None, vip_facilities=None, vip_talent_orbs=None, special_stages=None, character_settings=None, main_story_stages=None, event_stage_settings=None, lineup_settings=None, ototo_settings=None, dojo_score_settings=None, future_score_settings=None, access_tier="free"):
    def update(d):
        d["updated_at"] = time.time()
        _update_job(job_id, d)
    try:
        update({"status": "running", "started_at": time.time(), "log": "アカウントを作成中..."})

        cc = core.CountryCode.from_code("jp")
        gv = core.GameVersion(TARGET_GAME_VERSION_NUMBER)

        char_list = [c.strip() for c in char_list if str(c).strip().isdigit()]

        filename = ACCOUNT_TYPE_FILES.get(account_type_key, "Nyanko_new")
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), filename)
        if not os.path.exists(path):
            update({"status": "error", "error": f"エラー: {filename} が見つかりません。"})
            return

        count = max(1, min(MAX_COUNT, int(count)))
        accounts = []
        final_logs = []

        # テンプレートファイルはジョブ中に一度だけ読み込む。
        # 各アカウントには独立した core.Data コピーを渡すため、設定が混ざらない。
        template_data = core.Data.from_file(core.Path(path))

        for i in range(count):
            account_started = time.perf_counter()
            update({"log": f"アカウントを作成中... ({i+1}/{count})"})
            save = core.SaveFile(core.Data(template_data), cc=cc)
            ensure_latest_save_schema(save)
            handler = ServerHandler(save)

            create_started = time.perf_counter()
            if not handler.create_new_account():
                print(f"[PERF] create account {i+1}/{count}: {time.perf_counter() - create_started:.2f}s (failed)")
                update({"status": "error", "error": f"エラー: アカウント作成失敗 ({i+1}個目)。"})
                return
            print(f"[PERF] create_new_account {i+1}/{count}: {time.perf_counter() - create_started:.2f}s")

            apply_started = time.perf_counter()
            if i == 0:
                update({"log": "データを適用中..."})
                final_logs = _apply_all_segments(handler.save_file, selected, char_list, custom_amounts, custom_playtime, main_story_chapters, vip_items, legend_stages, vip_facilities, vip_talent_orbs, special_stages, character_settings, main_story_stages, event_stage_settings, lineup_settings, ototo_settings, dojo_score_settings, future_score_settings)
            else:
                _apply_all_segments(handler.save_file, selected, char_list, custom_amounts, custom_playtime, main_story_chapters, vip_items, legend_stages, vip_facilities, vip_talent_orbs, special_stages, character_settings, main_story_stages, event_stage_settings, lineup_settings, ototo_settings, dojo_score_settings, future_score_settings)
            print(f"[PERF] apply settings {i+1}/{count}: {time.perf_counter() - apply_started:.2f}s")

            codes_started = time.perf_counter()
            codes = handler.get_codes()
            print(f"[PERF] get_codes {i+1}/{count}: {time.perf_counter() - codes_started:.2f}s")
            if codes:
                accounts.append({"tc": codes[0], "ac": codes[1]})
            else:
                update({"status": "error", "error": f"エラー: 保存失敗 ({i+1}個目)。"})
                return
            print(f"[PERF] total account {i+1}/{count}: {time.perf_counter() - account_started:.2f}s")

        total_count = increment_usage_count()
        update({
            "status": "done",
            "accounts": accounts,
            "transfer_code": accounts[0]["tc"],
            "auth_code": accounts[0]["ac"],
            "applied": final_logs,
        })
        send_usage_log(
            access_tier,
            [f"新規アカウント作成 ×{len(accounts)}", *final_logs],
            total_count,
            USAGE_DB_PATH,
        )

    except Exception as e:
        update({"status": "error", "error": str(e)})
        print(traceback.format_exc())


class SafeCloneServerHandler(ServerHandler):
    """Create at most one copy account and snapshot it as soon as its ID exists."""

    def __init__(self, save_file, snapshot_callback=None, print=True):
        super().__init__(save_file, print=print)
        self.snapshot_callback = snapshot_callback
        self.account_assigned = False

    def get_password(self, tries=0):
        # BCSFE's default fallback calls create_new_account() again when account
        # setup communication fails. A clone must never silently abandon the
        # first issued account ID and create another one.
        password = self.get_stored_password()
        if password is not None:
            return password
        password = self.refresh_password()
        if password is not None:
            return password
        return self.get_password_new()

    def create_new_account(self, tries=1):
        new_inquiry_code = self.get_new_inquiry_code()
        if new_inquiry_code is None:
            return False

        self.save_file.inquiry_code = new_inquiry_code
        self.account_assigned = True
        self.remove_stored_auth_token()
        self.remove_stored_save_key_data()
        self.remove_stored_password()
        fail_text = "EXPECT_THIS_TO_FAIL"
        start_count = (40 - len(fail_text)) // 2
        end_count = 40 - len(fail_text) - start_count
        self.save_file.password_refresh_token = (
            "_" * start_count + fail_text + "_" * end_count
        )

        # ID発行直後に永続化。以降の認証通信が失敗しても管理パネルから
        # 同じコピーアカウントの再発行を試せる。
        if self.snapshot_callback is not None:
            self.snapshot_callback(self.save_file)

        password = self.get_password()
        auth_token = self.get_auth_token()
        save_key_data = self.get_save_key()
        self.update_managed_items()
        self.save_file.show_ban_message = False
        return password is not None and auth_token is not None and save_key_data is not None


def run_job_clone(job_id, operation_id, transfer_code, auth_code, count=1, access_tier="free"):
    def update(d):
        d["updated_at"] = time.time()
        _update_job(job_id, d)
    handler = None
    orig_codes = None
    copies = []
    active_copy_handler = None
    copy_recovery_pending = False
    try:
        update({"status": "running", "started_at": time.time(), "log": "サーバーに接続中..."})
        _update_operation(operation_id, status="running", error=None)

        cc = core.CountryCode.from_code("jp")
        gv = core.GameVersion(TARGET_GAME_VERSION_NUMBER)

        handler, result = ServerHandler.from_codes(
            transfer_code, auth_code, cc, gv, save_backup=False
        )
        if handler is None:
            update({"status": "error", "error": "エラー: コード無効。"})
            _close_operation(
                operation_id,
                status="error",
                recovery_status="not_available",
                error="コード無効のため、セーブデータは取得されていません。",
            )
            return

        update({"transfer_received": True, "log": "引き継ぎ取得済み・元アカウントを保存中..."})
        _save_operation_snapshot(operation_id, handler.save_file)

        update({"log": "セーブデータを取得中..."})
        save_data = handler.save_file.data

        # 最終転送POSTの応答が失われた場合、直後の再送は最初に発行された
        # コードを無効化し得る。BCSFE内部の段階別試行だけに限定する。
        orig_codes = handler.get_codes()
        if not orig_codes:
            error_text = (
                "引き継ぎ取得後、元アカウントの復旧コードを発行できませんでした。"
                "同じ操作を連続実行せず管理者へ連絡してください。"
            )
            update({
                "status": "error",
                "error": error_text,
                "transfer_received": True,
                "admin_recovery_required": True,
            })
            _update_operation(operation_id, status="error", error=error_text, recovery_status="reissue_failed")
            return

        # コピー作成中に後続処理が失敗しても、ここで確定した
        # 元アカウントの最新コードをエラー画面から回収できるよう保持する。
        update({
            "recovery_transfer_code": orig_codes[0],
            "recovery_auth_code": orig_codes[1],
            "admin_recovery_required": False,
            "log": "元アカウント保護済み・コピーを作成中...",
        })
        count = max(1, min(MAX_COUNT, int(count)))

        for i in range(count):
            copy_recovery_pending = True
            update({
                "log": f"コピーアカウントを作成中... ({i+1}/{count})",
                "return_pending": True,
            })
            copy_save = core.SaveFile(core.Data(save_data), cc=cc)
            ensure_latest_save_schema(copy_save)
            active_copy_handler = SafeCloneServerHandler(
                copy_save,
                snapshot_callback=lambda save: _save_operation_snapshot(operation_id, save),
            )
            if not active_copy_handler.create_new_account():
                error_text = f"エラー: コピーアカウント作成失敗 ({i+1}個目)。"
                if active_copy_handler.account_assigned:
                    # 新しいIDは既に発行済み。snapshotを破棄せず、同じIDの
                    # データから管理パネルで再発行できる状態にする。
                    update({
                        "status": "error", "error": error_text,
                        "admin_recovery_required": True,
                        "return_pending": False,
                    })
                    _update_operation(
                        operation_id,
                        status="error",
                        recovery_status="reissue_failed",
                        error=error_text,
                    )
                else:
                    copy_recovery_pending = False
                    update({
                        "status": "error", "error": error_text,
                        "admin_recovery_required": False,
                        "return_pending": False,
                    })
                    _close_operation(
                        operation_id,
                        status="error",
                        recovery_status="client_code_issued",
                        error=error_text,
                        issued_codes=orig_codes,
                    )
                return

            update({"log": f"コピーアカウントを保存中... ({i+1}/{count})"})
            _save_operation_snapshot(operation_id, active_copy_handler.save_file)
            copy_codes = active_copy_handler.get_codes()
            if not copy_codes:
                update({
                    "status": "error",
                    "error": f"エラー: コピーアカウントの保存失敗 ({i+1}個目)。",
                    "admin_recovery_required": True,
                    "return_pending": False,
                })
                _update_operation(
                    operation_id, status="error", recovery_status="reissue_failed",
                    error=f"コピーアカウントの保存失敗 ({i+1}個目)。",
                )
                return
            copies.append({"tc": copy_codes[0], "ac": copy_codes[1]})
            copy_recovery_pending = False
            update({"return_pending": False, "copies": copy.deepcopy(copies)})
            # このコピーは返却済みなので、次のコピー作成中は元アカウントを復旧対象に戻す。
            _save_operation_snapshot(operation_id, handler.save_file)
            active_copy_handler = None

        total_count = increment_usage_count()
        update({
            "status": "done",
            "orig_transfer_code": orig_codes[0],
            "orig_auth_code": orig_codes[1],
            "copies": copies,
            "copy_transfer_code": copies[0]["tc"],
            "copy_auth_code": copies[0]["ac"],
            "admin_recovery_required": False,
        })
        _close_operation(
            operation_id, status="done", recovery_status="not_needed"
        )
        send_usage_log(
            access_tier,
            [f"アカウント複製 ×{len(copies)}"],
            total_count,
            USAGE_DB_PATH,
        )

    except Exception as e:
        payload = {"status": "error", "error": _safe_error_message(e)}
        if orig_codes:
            payload.update({
                "recovery_transfer_code": orig_codes[0],
                "recovery_auth_code": orig_codes[1],
                "copies": copy.deepcopy(copies),
            })
        if handler is not None:
            payload.update({
                "transfer_received": True,
                "error": (
                    "引き継ぎ取得後に複製エラーが発生しました。"
                    "同じ操作を再実行せず、表示されたコードまたは管理パネルを使用してください。"
                ),
            })

        # コピーID発行後・コード返却前なら、そのコピーsnapshotを必ず保持。
        # 元アカウントの既知コードを例外処理で再発行して無効化しない。
        if copy_recovery_pending and active_copy_handler is not None:
            try:
                if active_copy_handler.account_assigned:
                    _save_operation_snapshot(operation_id, active_copy_handler.save_file)
            except Exception as snapshot_error:
                print(f"[ERROR] clone snapshot: {snapshot_error}")
            payload["admin_recovery_required"] = True
            payload["return_pending"] = False
            _update_operation(
                operation_id,
                status="error",
                error=payload["error"],
                recovery_status="reissue_failed",
            )
        elif orig_codes:
            payload["admin_recovery_required"] = False
            _close_operation(
                operation_id,
                status="error",
                recovery_status="client_code_issued",
                error=payload["error"],
                issued_codes=orig_codes,
            )
        elif handler is not None:
            payload["admin_recovery_required"] = True
            _update_operation(
                operation_id, status="error", error=payload["error"],
                recovery_status="reissue_failed",
            )
        else:
            payload["admin_recovery_required"] = False
            _close_operation(
                operation_id,
                status="error",
                recovery_status="not_available",
                error=payload["error"],
            )
        update(payload)
        print(traceback.format_exc())


class RecoveryServerHandler(ServerHandler):
    """Admin recovery must never silently turn the save into a new account."""
    def create_new_account(self, tries=3):
        return False



logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.FileHandler("bot.log", encoding="utf-8"),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

sys.path.append(os.path.join(os.getcwd(), "src"))

import importlib.util as _ilu, os as _os
_pp_path = _os.path.join(_os.path.dirname(__file__) if '__file__' in dir() else '.', 'paypayu.py')
if _os.path.exists(_pp_path):
    _pp_spec = _ilu.spec_from_file_location('paypayu', _pp_path)
    paypayu = _ilu.module_from_spec(_pp_spec)
    _pp_spec.loader.exec_module(paypayu)
    PAYPAY_AVAILABLE = True
else:
    try:
        import paypayu
        PAYPAY_AVAILABLE = True
    except ImportError:
        logger.warning("paypayu.py が見つかりません")
        PAYPAY_AVAILABLE = False

# =====================
# ここを編集してください
# =====================
# Discord Bot本体
_intents = discord.Intents.default()
_intents.guilds = True
_intents.members = True

BOT_TOKEN = os.getenv("DISCORD_BOT_TOKEN", "ここにとーくん").strip()
def _load_admin_ids():
    raw = os.getenv("ADMIN_IDS", "").strip()
    ids = []
    for part in raw.replace("、", ",").split(","):
        part = part.strip()
        if part.isdigit():
            ids.append(int(part))
    return ids

ADMIN_IDS = _load_admin_ids()

# サブ管理者:
# - .env の SUB_ADMIN_IDS に初期登録できる
# - /管理者権限付与 で追加したユーザーは sub_admin_ids.json に保存され、再起動後も維持
SUB_ADMIN_IDS_FILE = "sub_admin_ids.json"

def _load_sub_admin_ids():
    ids = []
    raw = os.getenv("SUB_ADMIN_IDS", "").strip()
    for part in raw.replace("、", ",").split(","):
        part = part.strip()
        if part.isdigit():
            ids.append(int(part))
    try:
        if os.path.exists(SUB_ADMIN_IDS_FILE):
            with open(SUB_ADMIN_IDS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, list):
                for value in data:
                    if str(value).isdigit():
                        ids.append(int(value))
    except Exception:
        logger.exception("Failed to load sub admin ids")
    return list(dict.fromkeys(ids))

SUB_ADMIN_IDS = _load_sub_admin_ids()

def _save_sub_admin_ids():
    try:
        with open(SUB_ADMIN_IDS_FILE, "w", encoding="utf-8") as f:
            json.dump(SUB_ADMIN_IDS, f, ensure_ascii=False, indent=2)
    except Exception:
        logger.exception("Failed to save sub admin ids")

def is_sub_admin(user_id: int) -> bool:
    return int(user_id) in SUB_ADMIN_IDS

def can_manage_prices_and_panels(user_id: int) -> bool:
    return int(user_id) in ADMIN_IDS or int(user_id) in SUB_ADMIN_IDS

def is_point_admin(user_id: int) -> bool:
    return can_manage_prices_and_panels(user_id)

ALLOWED_CHANNEL_IDS = []  # 空のままで全チャンネルOK


PAYPAY_DATA_FILE = "paypay_data.json"
ORDER_LOG_FILE = "order_log.json"
SETTINGS_FILE = "settings.json"
PRICE_FILE = "price_overrides.json"
POINT_PRICE_FILE = "point_price_overrides.json"
POINT_DB_FILE = "points.db"
POINT_UDID_API_BASE_URL = os.getenv("POINT_UDID_API_BASE_URL", "").strip().rstrip("/")
POINT_UDID_WEB_URL = os.getenv("POINT_UDID_WEB_URL", "").strip()
POINT_INVITE_HOLD_HOURS = 24
POINT_ACCOUNT_MIN_AGE_DAYS = 30
POINT_INVITE_REWARD = 5

# ポイント関連の同時処理を直列化する。
_POINT_DB_LOCK = threading.RLock()
_POINT_INVITE_CACHE = {}
_POINT_PENDING_INVITES = {}

def _point_db():
    conn = sqlite3.connect(POINT_DB_FILE, timeout=30)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA foreign_keys=ON")
    conn.execute("""CREATE TABLE IF NOT EXISTS point_balances (guild_id INTEGER NOT NULL, user_id INTEGER NOT NULL, points INTEGER NOT NULL DEFAULT 0, PRIMARY KEY(guild_id,user_id))""")
    conn.execute("""CREATE TABLE IF NOT EXISTS point_history (id INTEGER PRIMARY KEY AUTOINCREMENT, guild_id INTEGER NOT NULL, user_id INTEGER NOT NULL, delta INTEGER NOT NULL, reason TEXT NOT NULL, created_at TEXT NOT NULL)""")
    conn.execute("""CREATE TABLE IF NOT EXISTS point_invites (guild_id INTEGER NOT NULL, inviter_id INTEGER NOT NULL, invite_code TEXT PRIMARY KEY, created_at TEXT NOT NULL)""")
    conn.execute("""CREATE TABLE IF NOT EXISTS point_referrals (guild_id INTEGER NOT NULL, inviter_id INTEGER NOT NULL, member_id INTEGER NOT NULL, invite_code TEXT, joined_at TEXT NOT NULL, eligible_at TEXT, rewarded_at TEXT, udid TEXT, PRIMARY KEY(guild_id,member_id))""")
    conn.execute("""CREATE TABLE IF NOT EXISTS point_udid_bindings (guild_id INTEGER NOT NULL, user_id INTEGER NOT NULL, udid_hash TEXT NOT NULL, bound_at TEXT NOT NULL, PRIMARY KEY(guild_id,user_id), UNIQUE(guild_id,udid_hash))""")
    conn.execute("""CREATE TABLE IF NOT EXISTS point_auth_tokens (token TEXT PRIMARY KEY, guild_id INTEGER NOT NULL, user_id INTEGER NOT NULL, expires_at TEXT NOT NULL, used INTEGER NOT NULL DEFAULT 0)""")
    conn.commit()
    return conn

def _point_now():
    import datetime
    return datetime.datetime.now(datetime.timezone.utc)

def _point_get(guild_id, user_id):
    with _POINT_DB_LOCK:
        conn=_point_db()
        row=conn.execute("SELECT points FROM point_balances WHERE guild_id=? AND user_id=?",(int(guild_id),int(user_id))).fetchone()
        conn.close()
        return int(row[0]) if row else 0

def _point_change(guild_id, user_id, delta, reason):
    delta=int(delta)
    if delta==0: return _point_get(guild_id,user_id)
    with _POINT_DB_LOCK:
        conn=_point_db()
        conn.execute("INSERT OR IGNORE INTO point_balances(guild_id,user_id,points) VALUES(?,?,0)",(int(guild_id),int(user_id)))
        row=conn.execute("SELECT points FROM point_balances WHERE guild_id=? AND user_id=?",(int(guild_id),int(user_id))).fetchone()
        current=int(row[0])
        new=current+delta
        if new<0:
            conn.close()
            return None
        conn.execute("UPDATE point_balances SET points=? WHERE guild_id=? AND user_id=?",(new,int(guild_id),int(user_id)))
        conn.execute("INSERT INTO point_history(guild_id,user_id,delta,reason,created_at) VALUES(?,?,?,?,?)",(int(guild_id),int(user_id),delta,reason,_point_now().isoformat()))
        conn.commit(); conn.close(); return new

def _point_history(guild_id,user_id,limit=10):
    with _POINT_DB_LOCK:
        conn=_point_db(); rows=conn.execute("SELECT delta,reason,created_at FROM point_history WHERE guild_id=? AND user_id=? ORDER BY id DESC LIMIT ?",(int(guild_id),int(user_id),int(limit))).fetchall(); conn.close(); return rows

def _point_yen_price(key,guild_id):
    if not isinstance(key,str): return 0
    ck=canonical_price_key(key)
    if ck in globals().get("ITEM_CONFIG", {}): return get_price(ck,guild_id)
    if ck.startswith("__account_") and ck.endswith("__"):
        ak=ck[len("__account_"):-2]; return get_account_preset_price(ak,guild_id)
    special_defaults={
        "__clone__": globals().get("CLONE_PRICE_DEFAULT",100),
        "__full_edit__": globals().get("FULL_EDIT_PRICE_DEFAULT",500),
        "__recovery__": globals().get("RECOVERY_PRICE_DEFAULT",300),
    }
    if ck in special_defaults: return get_special_price(ck,special_defaults[ck],guild_id)
    for cfg in globals().get("CHARA_CONFIG",{}).values():
        if cfg.get("price_key")==ck: return get_special_price(ck,cfg.get("default",50),guild_id)
    if ck.startswith("custom_amount_"):
        kind=ck[len("custom_amount_"):]
        base=globals().get("CUSTOM_AMOUNT_PRICES",{}).get(kind,50)
        return get_special_price(ck,base,guild_id)
    return get_price(ck,guild_id)

def _point_default_price(key,guild_id):
    yen=_point_yen_price(key,guild_id)
    return max(1, (int(yen)+5)//10) if yen>0 else 0

def load_point_price_overrides(guild_id):
    try:
        with open(POINT_PRICE_FILE,'r',encoding='utf-8') as f: data=json.load(f)
    except Exception: data={}
    return {k:int(v) for k,v in (data.get(str(guild_id),{}) or {}).items() if str(v).lstrip('-').isdigit()}

def save_point_price_overrides(guild_id,data):
    try:
        with open(POINT_PRICE_FILE,'r',encoding='utf-8') as f: allp=json.load(f)
    except Exception: allp={}
    allp[str(guild_id)]={str(k):max(0,int(v)) for k,v in data.items()}
    with open(POINT_PRICE_FILE,'w',encoding='utf-8') as f: json.dump(allp,f,ensure_ascii=False,indent=2)

def get_point_price(key,guild_id):
    if not isinstance(key,str): return 0
    ov=load_point_price_overrides(guild_id)
    ck=canonical_price_key(key)
    if ck in ov: return int(ov[ck])
    return _point_default_price(ck,guild_id)

def _point_hash_udid(udid):
    secret=os.getenv('IDENTITY_HASH_KEY','point-udid').encode()
    return hashlib.sha256(secret+str(udid).encode()).hexdigest()

def _point_bind_udid(guild_id,user_id,udid):
    h=_point_hash_udid(udid)
    with _POINT_DB_LOCK:
        conn=_point_db()
        same=conn.execute("SELECT user_id FROM point_udid_bindings WHERE guild_id=? AND udid_hash=?",(int(guild_id),h)).fetchone()
        if same and int(same[0])!=int(user_id): conn.close(); return False,'already_used'
        conn.execute("INSERT INTO point_udid_bindings(guild_id,user_id,udid_hash,bound_at) VALUES(?,?,?,?) ON CONFLICT(guild_id,user_id) DO UPDATE SET udid_hash=excluded.udid_hash,bound_at=excluded.bound_at",(int(guild_id),int(user_id),h,_point_now().isoformat()))
        conn.commit(); conn.close(); return True,'ok'

def _point_udid_for_user(guild_id,user_id):
    with _POINT_DB_LOCK:
        conn=_point_db(); row=conn.execute("SELECT udid_hash FROM point_udid_bindings WHERE guild_id=? AND user_id=?",(int(guild_id),int(user_id))).fetchone(); conn.close(); return row[0] if row else None

def _point_create_auth_token(guild_id,user_id):
    secret=os.getenv("POINT_UDID_SHARED_SECRET","").strip()
    if not secret: return None
    import datetime, base64
    payload={"guild_id":int(guild_id),"user_id":int(user_id),"exp":int((_point_now()+datetime.timedelta(minutes=15)).timestamp())}
    raw=base64.urlsafe_b64encode(json.dumps(payload,separators=(",",":"),ensure_ascii=False).encode()).decode().rstrip("=")
    sig=hmac.new(secret.encode(),raw.encode(),hashlib.sha256).hexdigest()
    return raw+"."+sig

def _point_get_auth_token(token):
    with _POINT_DB_LOCK:
        conn=_point_db(); row=conn.execute("SELECT token,guild_id,user_id,expires_at,used FROM point_auth_tokens WHERE token=?",(token,)).fetchone(); conn.close()
    if not row or int(row['used']): return None
    try:
        if _point_now() > __import__('datetime').datetime.fromisoformat(row['expires_at']): return None
    except Exception: return None
    return dict(row)

def _point_mark_auth_used(token):
    with _POINT_DB_LOCK:
        conn=_point_db(); conn.execute("UPDATE point_auth_tokens SET used=1 WHERE token=?",(token,)); conn.commit(); conn.close()

def _point_is_eligible_member(member):
    import datetime
    if member.bot: return False
    age=(_point_now()-member.created_at).total_seconds()/86400
    joined=member.joined_at
    if joined is None: return False
    stay=(_point_now()-joined).total_seconds()/3600
    return age>=POINT_ACCOUNT_MIN_AGE_DAYS and stay>=POINT_INVITE_HOLD_HOURS

async def _point_cache_invites(guild):
    try:
        invites=await guild.invites()
    except Exception as e:
        logger.warning(f'ポイント招待一覧取得失敗 {guild.id}: {e}'); return
    cache={}
    with _POINT_DB_LOCK:
        conn=_point_db()
        for inv in invites:
            cache[inv.code]=int(inv.uses or 0)
            row=conn.execute('SELECT inviter_id FROM point_invites WHERE invite_code=?',(inv.code,)).fetchone()
            if row: _POINT_INVITE_CACHE[(guild.id,inv.code)]=(int(row[0]),int(inv.uses or 0))
        conn.close()

async def _point_fetch_bound_udid(member):
    if not POINT_UDID_API_BASE_URL: return None
    url=f"{POINT_UDID_API_BASE_URL}/check.php?discord_id={urllib.parse.quote(str(member.id))}"
    loop=asyncio.get_running_loop()
    def _fetch():
        try:
            r=requests.get(url,timeout=10)
            if r.status_code!=200: return None
            data=r.json()
            if data.get("status")!="allowed": return None
            return data.get("udid")
        except Exception:
            return None
    return await loop.run_in_executor(None,_fetch)

async def _point_process_pending_referrals():
    import datetime
    now=_point_now()
    with _POINT_DB_LOCK:
        conn=_point_db(); rows=conn.execute("SELECT guild_id,inviter_id,member_id,invite_code,joined_at FROM point_referrals WHERE rewarded_at IS NULL AND joined_at <= ?",((now-__import__('datetime').timedelta(hours=POINT_INVITE_HOLD_HOURS)).isoformat(),)).fetchall(); conn.close()
    for row in rows:
        guild=bot.get_guild(int(row['guild_id']))
        if not guild: continue
        member=guild.get_member(int(row['member_id']))
        if not member or not _point_is_eligible_member(member): continue
        udid=await _point_fetch_bound_udid(member)
        if not udid:
            continue
        udid_hash=_point_hash_udid(udid)
        with _POINT_DB_LOCK:
            conn=_point_db(); used=conn.execute("SELECT member_id FROM point_referrals WHERE guild_id=? AND rewarded_at IS NOT NULL AND udid=?",(guild.id,udid_hash)).fetchone(); conn.close()
        if used: continue
        if _point_change(guild.id,int(row['inviter_id']),POINT_INVITE_REWARD,f'招待報酬: <@{member.id}>') is None: continue
        with _POINT_DB_LOCK:
            conn=_point_db(); conn.execute("UPDATE point_referrals SET rewarded_at=?,udid=? WHERE guild_id=? AND member_id=?",(now.isoformat(),udid_hash,guild.id,member.id)); conn.commit(); conn.close()

async def _point_referral_worker():
    await bot.wait_until_ready()
    while not bot.is_closed():
        try: await _point_process_pending_referrals()
        except Exception: logger.exception('point referral worker error')
        await asyncio.sleep(300)


# 垢サービス系デフォルト価格
CLONE_PRICE_DEFAULT       = 100
FULL_EDIT_PRICE_DEFAULT   = 500
RECOVERY_PRICE_DEFAULT    = 300
ACCOUNT_PRESET_PRICE_DEFAULTS = {
    "new": 0,
    "beginner": 0,
    "intermediate": 0,
    "advanced": 0,
}
ACCOUNT_PRESET_LABELS = {
    "new": "初期垢",
    "beginner": "初心者垢",
    "intermediate": "中級者垢",
    "advanced": "上級者垢",
}

def get_account_preset_price(key: str, guild_id: int) -> int:
    return get_special_price(f"__account_{key}__", ACCOUNT_PRESET_PRICE_DEFAULTS.get(key, 0), guild_id)

# 指定キャラ系デフォルト価格
CHARA_UNLOCK_PRICE_DEFAULT  = 50
CHARA_LVMAX_PRICE_DEFAULT   = 50
CHARA_FORM_PRICE_DEFAULT    = 50
CHARA_DELETE_PRICE_DEFAULT   = 50
CHARA_LVMAX_PLUS_PRICE_DEFAULT = 50
CHARA_LEVEL_PRICE_DEFAULT    = 50
CHARA_FORM_SELECT_PRICE_DEFAULT = 50
CHARA_TALENT_PRICE_DEFAULT   = 100


ITEM_CONFIG = {
    # ━━ ステージクリア系 ━━
    "main_clear":         {"label": "メインステージ全クリア+お宝金",   "price": 100},
    "zombie_clear":       {"label": "メインゾンビステージ全クリア",    "price": 300},
    "old_legend_clear":   {"label": "旧レジェンド全クリア",           "price": 300},
    "true_legend_clear":  {"label": "真レジェンド全クリア",           "price": 300},
    "zero_legend_clear":  {"label": "零レジェンド全クリア",           "price": 300},
    "makai_clear":        {"label": "魔界編全クリア",                 "price": 300},
    "event_clear":        {"label": "イベントステージ全クリア",       "price": 500},
    # ━━ キャラ系 ━━
    "all_char_unlock":    {"label": "全キャラ開放",               "price": 100},
    "error_char_delete":  {"label": "エラーキャラ削除",           "price": 100},
    "all_char_lv_max":    {"label": "全キャラLvMAX",              "price": 100},
    "all_char_max_form":  {"label": "全キャラ最大形態",           "price": 100},
    "all_honnou_max":     {"label": "全キャラ本能全開放",         "price": 250},
    # ━━ その他 ━━
    "telop_delete":       {"label": "開放テロップ削除",           "price": 0},
    "slot_max":           {"label": "編成スロット数最大拡張",     "price": 50},
    "medal_all":          {"label": "にゃんこメダル全開放",       "price": 100},
    "enemy_book_all":     {"label": "敵キャラ図鑑全開放",         "price": 100},
    "user_rank_all":      {"label": "ユーザーランク報酬全受取",   "price": 50},
    "playtime_max":       {"label": "プレイ時間カンスト",         "price": 200},
    "gold_pass":          {"label": "ゴールド会員化",             "price": 200},
    "facility_max":       {"label": "施設LvMAX",                 "price": 100},
    "gamatoto_max":       {"label": "ガマトトLvMAX",              "price": 200},
    "gamatoto_legend":    {"label": "ガマトト助手全員レジェンド", "price": 200},
    "ad_free":            {"label": "広告非表示（β）",            "price": 50},
    "ototo_max":          {"label": "オトート全城強化LvMAX",      "price": 200},
    "shrine_max":         {"label": "にゃんこ神社LvMAX",         "price": 100},
    "future_score":       {"label": "未来編 採点スコア指定",       "price": 100},
    "dojo_score":         {"label": "道場スコア指定",             "price": 100},
    "legend_detail":      {"label": "レジェンドマップ詳細指定",    "price": 100},
    "ototo_detail":       {"label": "オトート・城強化詳細指定",      "price": 100},
    "lineup_custom":      {"label": "編成キャラ個別設定",         "price": 0},
    "labyrinth_detail":   {"label": "地底迷宮詳細指定",             "price": 100},
    "event_detail":       {"label": "イベントステージ詳細指定",      "price": 150},
    "main_stage_detail":  {"label": "メイン章・ステージ個別指定",   "price": 100},
    "special_stage_detail": {"label": "ゾンビ・魔界編詳細指定",      "price": 100},
    "facility_detail":   {"label": "施設ごとのレベル指定",          "price": 100},
    "talent_orb_detail": {"label": "本能玉名 → ランク 個別選択",     "price": 150},
    "event_ticket_detail": {"label": "イベントチケット 種類別選択",   "price": 100},
    "skip_tutorial":      {"label": "チュートリアルスキップ",       "price": 50},
    "hide_rank_up":       {"label": "ランクアップポップアップ非表示", "price": 50},
    "user_rank_rewards_unclaimed": {"label": "ユーザーランク報酬全未受取化", "price": 50},
    "catguide_rewards_claimed": {"label": "猫図鑑報酬全受取化", "price": 50},
    "catguide_rewards_unclaimed": {"label": "猫図鑑報酬全未受取化", "price": 50},
    "cat_scratcher_reset": {"label": "スクラッチ未実施化（引き直し）", "price": 50},
    "labyrinth_medals": {"label": "地底迷宮 勲章", "price": 100},
    "all_missions_clear": {"label": "全ミッションクリア（全種類）", "price": 100},
    "max_all_cats_plus": {"label": "全キャラLv.Max+", "price": 100},
    "talents_disable_all": {"label": "全キャラ本能無効", "price": 100},
}

# =====================
# データ管理
# =====================
def load_paypay_data() -> dict:
    if os.path.exists(PAYPAY_DATA_FILE):
        try:
            with open(PAYPAY_DATA_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except json.JSONDecodeError:
            return {}
    return {}

def save_paypay_data(data: dict):
    with open(PAYPAY_DATA_FILE, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=4, ensure_ascii=False)

def load_order_log() -> list:
    import datetime
    if os.path.exists(ORDER_LOG_FILE):
        try:
            with open(ORDER_LOG_FILE, "r", encoding="utf-8") as f:
                log = json.load(f)
        except json.JSONDecodeError:
            return []
    else:
        return []

    cutoff = datetime.datetime.now() - datetime.timedelta(days=1)
    log = [e for e in log if datetime.datetime.fromisoformat(e["timestamp"]) > cutoff]
    return log

def log_order(user_id: int, username: str, items: list, amount: int, status: str):
    import datetime
    log = load_order_log()
    log.append({
        "timestamp": datetime.datetime.now().isoformat(),
        "user_id": str(user_id),
        "username": username,
        "items": items,
        "amount": amount,
        "status": status,
    })
    with open(ORDER_LOG_FILE, "w", encoding="utf-8") as f:
        json.dump(log, f, indent=4, ensure_ascii=False)
    logger.info(f"[ORDER] {username}({user_id}) {items} {amount}円 [{status}]")

# =====================
# サーバー別設定管理
# =====================
def _load_all_settings() -> dict:
    if os.path.exists(SETTINGS_FILE):
        try:
            with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except json.JSONDecodeError:
            return {}
    return {}

def _save_all_settings(data: dict):
    with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=4, ensure_ascii=False)

def load_settings(guild_id: int) -> dict:
    return _load_all_settings().get(str(guild_id), {})

def save_settings(guild_id: int, data: dict):
    all_s = _load_all_settings()
    all_s[str(guild_id)] = data
    _save_all_settings(all_s)


async def safe_interaction_message_edit(interaction, **kwargs):
    """削除済み/期限切れのDiscordメッセージを編集してもBotが落ちないようにする。"""
    try:
        if interaction.message is not None:
            await interaction.message.edit(**kwargs)
            return True
    except discord.NotFound:
        logger.warning("操作元メッセージが既に削除されています。処理は継続します。")
    except discord.HTTPException as e:
        logger.warning(f"操作元メッセージの更新に失敗しました: {e}")
    return False


def register_panel_message(guild_id: int, panel_type: str, message):
    """設置したパネルのチャンネル/メッセージIDを保存する。値段変更時の再描画に使用。"""
    settings = load_settings(guild_id)
    panels = settings.setdefault("panel_messages", {})
    panels[panel_type] = {"channel_id": message.channel.id, "message_id": message.id}
    save_settings(guild_id, settings)


def get_registered_panel(guild_id: int, panel_type: str):
    return load_settings(guild_id).get("panel_messages", {}).get(panel_type)


async def refresh_registered_panel(guild_id: int, panel_type: str):
    """価格変更後、既設パネルのSelect内価格も現在価格へ更新する。"""
    info = get_registered_panel(guild_id, panel_type)
    if not info:
        return False
    try:
        channel = bot.get_channel(int(info["channel_id"])) or await bot.fetch_channel(int(info["channel_id"]))
        message = await channel.fetch_message(int(info["message_id"]))
        gid = int(guild_id)
        if panel_type == "main":
            embed = discord.Embed(
                title="にゃんこ大戦争 代行自販機",
                description="以下のセレクトから選択して購入してください。\n価格はセレクトメニュー内に表示されます",
                color=0x00cc88,
            )
            view = PanelView(gid)
        elif panel_type == "vip":
            embed = discord.Embed(
                title="にゃんこ大戦争 代行自販機",
                description="以下のセレクトから選択して購入してください。\n価格はセレクトメニュー内に表示されます",
                color=0x38bdf8,
            )
            view = VipPanelView(gid)
        elif panel_type == "new_account":
            embed = discord.Embed(
                title="にゃんこ大戦争 代行自販機",
                description="以下のセレクトから選択して購入してください。\n価格はセレクトメニュー内に表示されます",
                color=0x5865F2,
            )
            view = NewAccountOrderView(gid, "custom", "新規垢")
        elif panel_type == "chara":
            embed = discord.Embed(
                title="にゃんこ大戦争 代行自販機",
                description="以下のセレクトから選択して購入してください。\n価格はセレクトメニュー内に表示されます",
                color=0x00cc88,
            )
            view = CharaPanelView(gid)
        elif panel_type == "account":
            embed = discord.Embed(
                title="にゃんこ大戦争 代行自販機",
                description="以下のセレクトから選択して購入してください。\n価格はセレクトメニュー内に表示されます",
                color=0x5865F2,
            )
            view = AccountPresetView(gid)
        elif panel_type == "point":
            embed = discord.Embed(title="💰 にゃんこ大戦争 ポイント代行",description="ポイントで代行を購入できます。\n招待報酬：1人 +5pt",color=0xf5c542)
            view = VipPanelView(gid,payment_mode='points')
        else:
            return False
        await message.edit(embed=embed, view=view)
        return True
    except Exception as e:
        logger.warning(f"パネル再描画失敗 {guild_id}/{panel_type}: {e}")
        return False

# =====================
# サーバー別値段オーバーライド管理
# =====================
def _load_all_price_overrides() -> dict:
    if os.path.exists(PRICE_FILE):
        try:
            with open(PRICE_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except json.JSONDecodeError:
            return {}
    return {}

def _save_all_price_overrides(data: dict):
    with open(PRICE_FILE, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=4, ensure_ascii=False)

def load_price_overrides(guild_id: int) -> dict:
    raw = _load_all_price_overrides().get(str(guild_id), {}) or {}
    # 以前のバージョンで保存された別名キーも、読み込み時に正規キーへ寄せる。
    normalizer = globals().get("canonical_price_key")
    normalized = {}
    for k, v in raw.items():
        try:
            ck = normalizer(k) if normalizer else k
            normalized[ck] = int(v)
        except (TypeError, ValueError):
            continue
    return normalized

# 価格変更・購入処理で必ず同じキーを使うための正規化表。
# UI側の値を直接価格キーとして保存/計算することはしない。
PRICE_KEY_ALIASES = {
    "main_story_clear": "main_clear",
    "zombie_clear": "zombie_clear",
    "aku_clear": "makai_clear",
    "legend_clear": "old_legend_clear",
    "true_legend_clear": "true_legend_clear",
    "zero_legend_clear": "zero_legend_clear",
    "all_stage_clear": "event_clear",
    "gamatoto_max": "gamatoto_max",
    "gamatoto_helpers": "gamatoto_legend",
    "ototo_max": "ototo_max",
    "cat_shrine_max": "shrine_max",
    "base_upgrades_max": "facility_max",
    "gold_membership": "gold_pass",
    "slots_max": "slot_max",
    "medals_all": "medal_all",
    "unlock_enemy_guide": "enemy_book_all",
    "user_rank_rewards_claimed": "user_rank_all",
    "add_playtime_720h": "playtime_max",
    "unlock_all_cats": "all_char_unlock",
    "max_all_cats": "all_char_lv_max",
    "true_form_all": "all_char_max_form",
    "talents_all": "all_honnou_max",
    "remove_error_cats": "error_char_delete",
    "new": "__account_new__",
    "beginner": "__account_beginner__",
    "intermediate": "__account_intermediate__",
    "advanced": "__account_advanced__",
}

def canonical_price_key(key: str) -> str:
    if not isinstance(key, str):
        return key
    return PRICE_KEY_ALIASES.get(key, key)

def save_price_overrides(guild_id: int, data: dict):
    # 保存時も必ず正規キーへ統一する。
    normalized = {}
    for k, v in (data or {}).items():
        normalized[canonical_price_key(k)] = int(v)
    all_p = _load_all_price_overrides()
    all_p[str(guild_id)] = normalized
    _save_all_price_overrides(all_p)

def get_price(key: str, guild_id: int) -> int:
    """表示・合計・決済の全箇所で同じ正規価格キーを使う。"""
    # 価格キー以外（整数など）が誤って渡っても落ちないようにする。
    if not isinstance(key, str):
        return 0
    key = canonical_price_key(key)
    ov = load_price_overrides(guild_id)

    if key in ITEM_CONFIG:
        default = ITEM_CONFIG[key]["price"]
        return int(ov.get(key, default) or 0)

    if key.startswith("__account_") and key.endswith("__"):
        account_key = key[len("__account_"):-2]
        return int(ov.get(key, ACCOUNT_PRESET_PRICE_DEFAULTS.get(account_key, 0)) or 0)

    if key in {"future_score|", "future_score_individual|"} or (isinstance(key, str) and key.startswith(("future_score|", "future_score_individual|"))):
        return get_special_price("future_score", ITEM_CONFIG["future_score"]["price"], guild_id)

    if isinstance(key, str):
        for prefix, base in (("legend_detail|", "legend_detail"), ("ototo_detail|", "ototo_detail"), ("lineup_detail|", "lineup_custom"), ("labyrinth_detail|", "labyrinth_detail"), ("event_detail|", "event_detail"), ("dojo_score|", "dojo_score")):
            if key.startswith(prefix):
                return get_special_price(base, ITEM_CONFIG.get(base, {"price":0})["price"], guild_id)

    if isinstance(key, str) and key.startswith("custom_amount|"):
        parts = key.split("|", 2)
        if len(parts) == 3 and parts[1] in CUSTOM_AMOUNT_PRICES:
            kind = parts[1]
            return get_special_price(f"custom_amount_{kind}", CUSTOM_AMOUNT_PRICES[kind], guild_id)

    # 未登録キーは勝手に50円にしない。
    return 0

def get_special_price(key: str, default: int, guild_id: int) -> int:
    ov = load_price_overrides(guild_id)
    return ov.get(key, default)

def get_jisseki_channel_id(guild_id: int):
    settings = load_settings(guild_id)
    val = settings.get("jisseki_channel_id")
    return int(val) if val else None

def is_admin(user_id: int) -> bool:
    return user_id in ADMIN_IDS

# =====================
# bcsfe セーブ編集
# =====================
_valid_cat_max_cache: int | None = None

def _get_valid_cat_max() -> int:
    """battlecats-db.com の最大キャラID+1を返す。取得失敗またはIDが674以下なら674を使用。
    ID674以降はエラーキャラ扱い（画像の皇獣ガオウ=673が最大有効キャラ）。"""
    global _valid_cat_max_cache
    if _valid_cat_max_cache is not None:
        return _valid_cat_max_cache
    HARDCODED_MAX = 674  # ID673(皇獣ガオウ)が現在の最大有効キャラ
    try:
        import urllib.request, re
        url = "https://battlecats-db.com/unit/"
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        with urllib.request.urlopen(req, timeout=8) as r:
            html = r.read().decode("utf-8", errors="ignore")
        ids = [int(m) for m in re.findall(r'/unit/(\d+)\.html', html)]
        if ids:
            max_id = max(ids) + 1
            # 取得値が合理的な範囲内のみ使用
            if 500 <= max_id <= 2000:
                _valid_cat_max_cache = max_id
                logger.info(f"battlecats-db 有効キャラID最大値: {max_id}")
                return max_id
    except Exception as e:
        logger.warning(f"battlecats-db取得失敗、fallback={HARDCODED_MAX}: {e}")
    _valid_cat_max_cache = HARDCODED_MAX
    return HARDCODED_MAX


def _sv(save_file, attr: str, value: int):
    """
    bcsfeカスタム整数型に対応した汎用セッター
    試す順: .value= → 直接代入 → .set()
    """
    try:
        obj = getattr(save_file, attr)
        try:
            obj.value = value
            return
        except (AttributeError, TypeError):
            pass
        try:
            setattr(save_file, attr, value)
            return
        except (TypeError, AttributeError):
            pass
        try:
            obj.set(value)
        except Exception:
            pass
    except Exception as e:
        logger.warning(f"_sv({attr}, {value}) 失敗: {e}")


def _sv_list(save_file, attr: str, value: int):
    """
    bcsfeカスタムリスト型に対応した汎用セッター（全要素を同じ値に）
    試す順: [i].value= → [i]= → [i].set()
    """
    try:
        lst = getattr(save_file, attr)
        for i in range(len(lst)):
            try:
                lst[i].value = value
            except (AttributeError, TypeError):
                try:
                    lst[i] = value
                except (TypeError, AttributeError):
                    try:
                        lst[i].set(value)
                    except Exception:
                        pass
    except Exception as e:
        logger.warning(f"_sv_list({attr}, {value}) 失敗: {e}")


def _iter_cats(save_file):
    """
    bcsfe の Cats オブジェクトから実際のキャラリストを取り出す。
    save_file.cats は Cats オブジェクト → .cats でリスト取得。
    """
    try:
        cats_obj = save_file.cats

        for attr in ("cats", "data", "_cats", "items"):
            try:
                lst = getattr(cats_obj, attr, None)
                if lst is not None and hasattr(lst, "__iter__"):
                    return list(lst)
            except Exception:
                pass

        try:
            return list(cats_obj)
        except Exception:
            pass
    except Exception:
        pass
    return []


def _auto_run(func, save_file, inputs: list):
    """
    bcsfe CLI関数を自動入力でサイレント実行する。
    inputs: 先頭の応答リスト。不足分はフォールバックで補充。
    """
    import sys, io

    fallback = (
        ["1", "10", "y", "999", "4", "0", "1", "10", "y", "999", "4", "0"] * 20
    )
    responses = list(inputs) + fallback
    fake_stdin = io.StringIO("\n".join(str(r) for r in responses) + "\n")
    old_stdin, old_stdout, old_stderr = sys.stdin, sys.stdout, sys.stderr
    sys.stdin  = fake_stdin
    sys.stdout = io.StringIO()
    sys.stderr = io.StringIO()
    try:
        func(save_file)
    except (EOFError, StopIteration, SystemExit):
        pass
    except Exception as e:
        sys.stdout = old_stdout
        sys.stderr = old_stderr
        logger.warning(f"[_auto_run] {getattr(func, '__name__', str(func))} エラー: {e}")
        return
    finally:
        sys.stdin  = old_stdin
        sys.stdout = old_stdout
        sys.stderr = old_stderr


def _clear_chapters(sf, chapters, name, logger):
    """型に応じて全クリア処理を分岐"""
    try:
        ctype = type(chapters).__name__

        # ===== ZeroLegendsChapters / GauntletChapters: clear_stage API =====
        if hasattr(chapters, "clear_stage"):
            total_maps = len(chapters.chapters)
            cleared = 0
            for mid in range(total_maps):
                try: total_stars = chapters.get_total_stars(mid)
                except: total_stars = 1
                for star in range(total_stars):
                    try: total_stages = chapters.get_total_stages(mid, star)
                    except: total_stages = 48
                    # total_stages を Chapter に設定（clear_progress計算のため必須）
                    try: chapters.set_total_stages(mid, total_stages)
                    except: pass
                    for stage in range(total_stages):
                        try: chapters.clear_stage(mid, star, stage, 1, True)
                        except: pass
                cleared += 1
            logger.info(f"{name}: {cleared}ch 完了")
            return cleared

        # ===== ExChapters (旧レジェンド): chapters[i].stages[j] に clear_times =====
        logger.info(f"{name} ctype={ctype}")
        if ctype == "ExChapters" or hasattr(chapters, "stages") and not hasattr(chapters, "chapters"):
            cleared = 0
            try:
                ch_list = chapters.chapters
                if ch_list:
                    _ch0 = ch_list[0]
                    _ch0_attrs = [a for a in dir(_ch0) if not a.startswith("_")]
                    logger.info(f"{name} ex ch0 attrs: {_ch0_attrs}")
                    if hasattr(_ch0, "stages") and _ch0.stages:
                        _st0_attrs = [a for a in dir(_ch0.stages[0]) if not a.startswith("_")]
                        logger.info(f"{name} ex stage0 attrs: {_st0_attrs}")
            except: pass
            try:
                ch_list = chapters.chapters
            except:
                ch_list = []

            if ch_list:
                try:
                    _v0 = ch_list[0].stages[0].clear_amount
                    logger.info(f"{name} clear_amount type={type(_v0).__name__}, val={_v0}")
                except: pass
                try:
                    _ch0_val_attrs = {a: getattr(ch_list[0], a, None) for a in dir(ch_list[0]) if not a.startswith("_") and a not in ("deserialize","init","read","serialize","stages","write")}
                    logger.info(f"{name} ch0 values: {_ch0_val_attrs}")
                except: pass
            for _ci, ch in enumerate(ch_list):
                try:
                    stages = ch.stages
                    _before = getattr(stages[0], "clear_amount", "?") if stages else "?"
                    for st in stages:

                        _set = False
                        for _iattr in ("_clear_amount", "__clear_amount", "_ClearAmount", "_clear_count"):
                            _v = st.__dict__.get(_iattr) or getattr(st, _iattr, None)
                            if _v is not None and hasattr(_v, "value"):
                                try: _v.value = 1; _set = True; break
                                except: pass
                        if not _set:
                            try: st.clear_amount = 1
                            except: pass
                    _after = getattr(stages[0], "clear_amount", "?") if stages else "?"
                    if _ci == 0:

                        _st0_dict = stages[0].__dict__ if stages else {}
                        logger.info(f"{name} ch[0] before={_before} after={_after} st_dict={list(_st0_dict.keys())[:8]}")
                    cleared += 1
                except: pass
            logger.info(f"{name}: {cleared}ch 完了")
            return cleared

        if ctype == "Outbreaks" or hasattr(chapters, "clear_outbreak"):
            cleared = 0
            try:

                try: chapters.read_chapters()
                except: pass
                ch_list = chapters.chapters
                logger.info(f"{name} after read_chapters: len={len(ch_list)}, ob[0]_attrs={[a for a in dir(ch_list[0]) if not a.startswith('_')] if ch_list else []}")
                for _oi, ob in enumerate(ch_list):
                    _tid = None
                    for _fn_args in [(), (sf,)]:
                        try:
                            _t = ob.get_true_id(*_fn_args)
                            if _t is not None: _tid = int(_t); break
                        except: pass
                    if _tid is None:
                        try:
                            _raw = ob.id
                            _tid = int(_raw.value) if hasattr(_raw,"value") else int(_raw)
                        except: pass
                    if _tid is None: _tid = _oi
                    if _oi < 3:
                        logger.info(f"{name} ob[{_oi}] tid={_tid}")
                    for _try_tid in [_tid, _oi, _oi + 1]:
                        try:
                            chapters.clear_outbreak(_try_tid)
                            cleared += 1; break
                        except Exception as _e:
                            if _oi < 2: logger.warning(f"{name} clear_outbreak({_try_tid}) error: {_e}")
                    else:
                        cleared += 1
            except Exception as _e:
                logger.warning(f"{name} outbreaks error: {_e}")
            logger.info(f"{name}: {cleared}ch 完了")
            return cleared

        if ctype == "AkuChapters" or hasattr(chapters, "edit_aku_chapters"):

            cleared = 0
            try:
                outer_list = chapters.chapters
                if outer_list:
                    _c0 = outer_list[0]
                    _c0_attrs = [a for a in dir(_c0) if not a.startswith("_")]
                    logger.info(f"{name} inner ch attrs: {_c0_attrs}")
                    if hasattr(_c0, "chapters") and _c0.chapters:
                        _cc0 = _c0.chapters[0]
                        _cc0_attrs = [a for a in dir(_cc0) if not a.startswith("_")]
                        logger.info(f"{name} innermost attrs: {_cc0_attrs}")
                for ch in outer_list:
                    try:
                        if hasattr(ch, "chapters"):
                            for star_ch in ch.chapters:
                                if hasattr(star_ch, "stages"):
                                    _stages = star_ch.stages
                                    if _stages:
                                        _st0_attrs = [a for a in dir(_stages[0]) if not a.startswith("_")]
                                        logger.info(f"{name} aku stage0 attrs: {_st0_attrs}")
                                    for st in _stages:

                                        try: st.clear_times.value = 1; continue
                                        except: pass

                                        try:
                                            if callable(st.clear_stage): st.clear_stage()
                                        except: pass

                                    if hasattr(star_ch, "write_stages"):
                                        try: star_ch.write_stages(_stages)
                                        except: pass

                                    try:
                                        _last = len(_stages) - 1
                                        if hasattr(star_ch, "current_stage"):
                                            try: star_ch.current_stage.value = _last
                                            except: star_ch.current_stage = _last
                                    except: pass
                        cleared += 1
                    except Exception as _e:
                        logger.warning(f"{name} aku ch error: {_e}")
            except Exception as _e:
                logger.warning(f"{name} aku error: {_e}")
            logger.info(f"{name}: {cleared}ch 完了")
            return cleared

        logger.warning(f"{name}: 未知の型 {ctype}")
        return 0
    except Exception as e:
        logger.warning(f"{name} 失敗: {e}")
        return 0

def apply_chara_edits(save_file, service_label: str, chara_ids_str: str) -> list:

    try:

        raw_ids = [int(x.strip()) for x in chara_ids_str.replace("、", ",").split(",") if x.strip().isdigit()]
        ids = [i - 1 for i in raw_ids] 
    except Exception:
        ids = []
    if not ids:
        return []

    applied = []
    for cat_id, display_id in zip(ids, raw_ids):
        try:
            cat = None
            for candidate in save_file.cats.get_all_cats():
                try: cid = int(candidate.id) if not hasattr(candidate.id, 'value') else int(candidate.id.value)
                except: continue
                if cid == cat_id:
                    cat = candidate
                    break

            if cat is None:
                logger.warning(f"[apply_chara_edits] 表示ID:{display_id}(内部:{cat_id}) キャラが見つからない")
                continue

            if "開放" in service_label:
                cat.unlock(save_file)

            elif "削除" in service_label:
                try:
                    cat.remove(save_file)
                except Exception:
                    try:
                        cat.lock(save_file)
                    except Exception:
                        try:
                            cat.unlock_state = False
                        except Exception:
                            pass

            elif "Lv.Max+" in service_label:
                try:
                    from bcsfe import core as _c
                    pu = _c.PowerUpHelper(cat, save_file)
                    cat.upgrade.base = pu.get_max_possible_base() - 1
                    cat.upgrade.plus = pu.get_max_possible_plus()
                except Exception:
                    cat.upgrade.base = 29
                    cat.upgrade.plus = 0

            elif "Lv.Max" in service_label or "LvMAX" in service_label or "Lv MAX" in service_label:
                try:
                    from bcsfe import core as _c
                    pu = _c.PowerUpHelper(cat, save_file)
                    cat.upgrade.base = pu.get_max_possible_base() - 1
                    cat.upgrade.plus = 0
                except Exception:
                    cat.upgrade.base = 29
                    cat.upgrade.plus = 0

            elif "形態" in service_label:
                for fattr in ("current_form", "form", "cat_form", "evolve"):
                    try:
                        obj = getattr(cat, fattr, None)
                        if obj is None: continue
                        try: obj.value = 2
                        except: setattr(cat, fattr, 2)
                        break
                    except: pass

            applied.append(f"{service_label}[ID:{display_id}]")
            logger.info(f"[apply_chara_edits] 表示ID:{display_id}(内部:{cat_id}) {service_label} 完了")
        except Exception as e:
            logger.warning(f"[apply_chara_edits] 表示ID:{display_id} 失敗: {e}")

    return applied


# vip.html の「指定個数」用。キーは custom_amount|種類|数量 の形式で保持する。
CUSTOM_AMOUNT_PRICES = {
    "catfood": 50, "xp": 50, "np": 50,
    "normal_tickets": 50, "rare_tickets": 50,
    "platinum_tickets": 50, "legend_tickets": 50,
    "leadership": 50, "battle_items": 50, "catamins": 50,
    "catseyes": 100, "base_materials": 50, "matatabi": 100,
    "talent_orbs": 250, "event_tickets": 100,
    "base_upgrades": 50, "playtime": 50,
}
CUSTOM_AMOUNT_BASE = CUSTOM_AMOUNT_PRICES

def make_custom_amount_key(kind: str, amount: int) -> str:
    return f"custom_amount|{kind}|{max(0, int(amount))}"

def parse_custom_amount_key(key: str):
    if not isinstance(key, str) or not key.startswith("custom_amount|"):
        return None
    parts = key.split("|", 2)
    if len(parts) != 3 or parts[1] not in CUSTOM_AMOUNT_BASE:
        return None
    try:
        return parts[1], max(0, int(parts[2]))
    except ValueError:
        return None

def custom_amount_label(kind: str, amount: int) -> str:
    labels = {
        "catfood":"猫缶", "xp":"XP", "np":"NP", "normal_tickets":"にゃんこチケット",
        "rare_tickets":"レアチケット", "platinum_tickets":"プラチナチケット",
        "legend_tickets":"レジェンドチケット", "leadership":"リーダーシップ",
        "battle_items":"バトルアイテム全種", "catamins":"ネコビタン全種",
        "catseyes":"キャッツアイ全種", "base_materials":"城素材全種",
        "matatabi":"マタタビ全種", "talent_orbs":"本能玉全種",
        "event_tickets":"イベントチケット全種", "base_upgrades":"全施設",
        "playtime":"プレイ時間（時間）",
    }
    unit = "時間" if kind == "playtime" else "個"
    return f"{labels.get(kind, kind)} {amount:,}{unit}（指定）"

def apply_advanced_item_key(save_file, key: str):
    """Discordの詳細UIで生成したキーを、vip.htmlと同じ保存処理へ接続する。"""
    if not isinstance(key, str) or "|" not in key:
        return None
    prefix, payload = key.split("|", 1)
    try:
        data = json.loads(payload)
    except Exception:
        return [f"{prefix}（設定データ不正）"]
    try:
        if prefix == "main_stage_detail":
            return apply_main_story_stages(save_file, data)
        if prefix == "special_stage_detail":
            return apply_special_stages(save_file, data)
        if prefix == "legend_detail":
            return apply_legend_stages(save_file, data)
        if prefix == "ototo_detail":
            return apply_ototo_settings(save_file, data)
        if prefix == "lineup_detail":
            return apply_lineup_settings(save_file, data)
        if prefix == "labyrinth_detail":
            return apply_labyrinth_characters(save_file, data)
        if prefix == "event_detail":
            return apply_event_stage_settings(save_file, data)
        if prefix == "facility_detail":
            return apply_vip_facilities(save_file, data)
        if prefix == "talent_orb_detail":
            return apply_vip_talent_orbs(save_file, data)
        if prefix == "event_ticket_detail":
            return apply_vip_items(save_file, {"event_tickets": data})
    except Exception:
        logger.exception("advanced item apply failed: %s", key)
        return [f"{prefix}（適用失敗）"]
    return None


def apply_edits(save_file, item_keys: list) -> list:
    applied = []
    for key in item_keys:
        try:
            sf = save_file

            if isinstance(key, str) and key.startswith("future_score_individual|"):
                try:
                    _, _chapter, _payload = key.split("|", 2)
                    chapter_pos=int(_chapter); scores=json.loads(_payload)
                    real_id=MAIN_STORY_REAL_INDEX[chapter_pos]
                    chapter=sf.story.chapters[real_id]
                    stages=chapter.get_valid_treasure_stages()
                    if isinstance(scores,dict):
                        for raw_stage, raw_score in scores.items():
                            sid=int(raw_stage)
                            if 0 <= sid < len(chapter.stages): chapter.stages[sid].itf_timed_score=int(raw_score)
                    else:
                        for sid, raw_score in enumerate(scores):
                            if sid < len(stages): stages[sid].itf_timed_score=int(raw_score)
                    applied.append(f"{MAIN_STORY_CHAPTER_LABELS[chapter_pos]} 個別採点スコア")
                except Exception as e:
                    logger.exception("future_score_individual apply failed: %s", e); applied.append("未来編スコア個別指定（適用失敗）")
                continue

            if isinstance(key, str) and key.startswith("future_score|"):
                try:
                    _, _chapter, _score = key.split("|", 2)
                    chapter_pos=int(_chapter); real_id=MAIN_STORY_REAL_INDEX[chapter_pos]; chapter=sf.story.chapters[real_id]
                    stages=chapter.get_valid_treasure_stages()
                    if _score.startswith("random:"):
                        scores=json.loads(_score[len("random:"):])
                        for sid, raw_score in enumerate(scores):
                            if sid < len(stages): stages[sid].itf_timed_score=int(raw_score)
                        applied.append(f"{MAIN_STORY_CHAPTER_LABELS[chapter_pos]} 採点スコアランダム")
                    else:
                        score=int(_score)
                        for stage in stages: stage.itf_timed_score=score
                        applied.append(f"{MAIN_STORY_CHAPTER_LABELS[chapter_pos]} 採点スコア({score})")
                except Exception as e:
                    logger.exception("future_score apply failed: %s", e); applied.append("未来編 採点スコア（適用失敗）")
                continue

            if isinstance(key,str) and key.startswith("dojo_score|"):
                try:
                    score=int(key.split("|",1)[1])
                    applied.extend(apply_dojo_score_settings(sf,{"hall_of_initiates":score}))
                except Exception as e:
                    logger.exception("dojo score apply failed: %s",e); applied.append("道場スコア（適用失敗）")
                continue

            # 指定個数キーは JSON の詳細指定キーより先に処理する。
            # custom_amount|catfood|1000 のようなキーを
            # apply_advanced_item_key() に先に渡すと「設定データ不正」になるため。
            custom = parse_custom_amount_key(key)
            if custom is not None:
                kind, amount = custom
                try:
                    if kind == "catfood": sf.catfood = amount
                    elif kind == "xp": sf.xp = amount
                    elif kind == "np": sf.np = amount
                    elif kind == "normal_tickets": sf.normal_tickets = amount
                    elif kind == "rare_tickets": sf.rare_tickets = amount
                    elif kind == "platinum_tickets": sf.platinum_tickets = amount
                    elif kind == "legend_tickets": sf.legend_tickets = amount
                    elif kind == "leadership": sf.leadership = amount
                    elif kind == "battle_items":
                        for x in sf.battle_items.items: x.amount=amount
                    elif kind == "catamins": sf.catamins=[amount]*len(sf.catamins)
                    elif kind == "catseyes": sf.catseyes=[amount]*len(sf.catseyes)
                    elif kind == "base_materials":
                        for x in sf.ototo.base_materials.materials: x.amount=amount
                    elif kind == "matatabi": sf.catfruit=[amount]*len(sf.catfruit)
                    elif kind == "talent_orbs":
                        for oid in _latest_talent_orb_ids(): sf.talent_orbs.set_orb(oid,amount)
                    elif kind == "event_tickets":
                        for attr in ("event_capsules","lucky_tickets","event_capsules_2"):
                            obj=getattr(sf,attr,None)
                            if obj is not None:
                                for x in obj:
                                    try: x.amount=amount
                                    except Exception: pass
                    elif kind == "base_upgrades":
                        # 施設の一括指定は既存の汎用VIP施設処理を優先。
                        facilities={i:amount for i in range(len(getattr(sf.special_skills,"skills",[])))}
                        logs=apply_vip_facilities(sf,facilities); applied.extend(logs)
                    elif kind == "playtime":
                        seconds=amount*3600
                        if hasattr(sf,"play_time"):
                            try: sf.play_time=seconds
                            except Exception:
                                try: sf.play_time.value=seconds
                                except Exception: pass
                    applied.append(custom_amount_label(kind, amount))
                except Exception as e:
                    logger.exception("custom amount apply failed: %s", e)
                    applied.append(f"{custom_amount_label(kind,amount)}（適用失敗）")
                continue

            advanced_applied = apply_advanced_item_key(sf, key)
            if advanced_applied is not None:
                applied.extend(advanced_applied)
                continue

            def sv(attr, val):

                try:
                    obj = getattr(sf, attr)
                    try: obj.value = val; return
                    except: pass
                    try: setattr(sf, attr, val); return
                    except: pass
                    try: obj.set(val)
                    except: pass
                except Exception as e:
                    logger.warning(f"sv({attr},{val}): {e}")

            def sv_list(attr, val, sub=None):

                try:
                    lst = getattr(sf, attr)
                    if sub:
                        lst = getattr(lst, sub)
                    for i in range(len(lst)):
                        try: lst[i].value = val
                        except:
                            try: lst[i] = val
                            except: pass
                except Exception as e:
                    logger.warning(f"sv_list({attr},{val}): {e}")

            def sv_list_multi(attrs, val):

                for attr in attrs:
                    try:
                        lst = getattr(sf, attr, None)
                        if lst is None: continue
                        if hasattr(lst, 'items'): lst = lst.items
                        elif hasattr(lst, 'data'): lst = lst.data
                        for i in range(len(lst)):
                            try: lst[i].value = val
                            except:
                                try: lst[i] = val
                                except: pass
                        return True
                    except: pass
                return False

            if key == "main_clear":
                from bcsfe import core as _c
                # ストーリー全クリア
                try:
                    _auto_run(_c.game.map.story.StoryChapters.clear_story, sf, ["10"])
                    logger.info("main_clear: clear_story 完了")
                except Exception as _e:
                    logger.warning(f"main_clear clear_story 失敗: {_e}")
                # お宝金 ① edit_treasures _auto_run（"0"*20+"3"*20 が正しい入力パターン）
                try:
                    _auto_run(_c.game.map.story.StoryChapters.edit_treasures, sf,
                              ["0"] * 20 + ["3"] * 20)
                    logger.info("main_clear: お宝金(_auto_run) 完了")
                except Exception as _e:
                    logger.warning(f"main_clear edit_treasures 失敗: {_e}")
                # お宝金 ② chapter.stages[i] の treasure 属性を探索
                try:
                    _tr_cnt = 0
                    _story = sf.story
                    _chl = list(_story.chapters) if hasattr(_story, "chapters") else [_story]
                    # stage[0] の属性もデバッグ表示
                    if _chl and hasattr(_chl[0], "stages") and len(_chl[0].stages) > 0:
                        _st0 = _chl[0].stages[0]
                        _st0_attrs = [a for a in dir(_st0) if not a.startswith("_") and not callable(getattr(_st0,a,None))]
                        logger.info(f"main_clear debug: stage[0]属性={_st0_attrs[:15]}")
                    for _ch in _chl:
                        # まず chapter 直下の treasure 系属性を試す
                        for _tattr in ("treasures", "treasure", "treasure_data"):
                            _tlist = getattr(_ch, _tattr, None)
                            if _tlist is None or not hasattr(_tlist, "__iter__"): continue
                            for _tr in _tlist:
                                for _sattr in ("state","value","treasure_state","status"):
                                    try:
                                        _sv = getattr(_tr, _sattr, None)
                                        if _sv is None: continue
                                        try: _sv.value = 3; _tr_cnt += 1; break
                                        except:
                                            try: setattr(_tr, _sattr, 3); _tr_cnt += 1; break
                                            except: pass
                                    except: pass

                        for _st in getattr(_ch, "stages", []):
                            _tv = getattr(_st, "treasure", None)
                            if _tv is None: continue

                            try: _tv.value = 3; _tr_cnt += 1; continue
                            except: pass

                            try: setattr(_st, "treasure", 3); _tr_cnt += 1; continue
                            except: pass
                    logger.info(f"main_clear: お宝金 直接セット {_tr_cnt}個 完了")
                except Exception as _e2:
                    logger.warning(f"main_clear お宝金 直接セット失敗: {_e2}")

            elif key == "zombie_clear":
                try:
                    from bcsfe.core.game.map.outbreaks import Outbreak as _ObStage
                    _ob = sf.outbreaks
                    _ok_cnt = 0
                    for _cid, _ch in list(_ob.chapters.items()):

                        for _sid in range(48):
                            _ch.outbreaks[_sid] = _ObStage(True)
                            _ok_cnt += 1
                    _ob.current_outbreaks = {}
                    logger.info(f"zombie_clear: {_ok_cnt}ステージ完了 current_outbreaks=cleared")
                except Exception as _e:
                    logger.warning(f"zombie_clear失敗: {_e}")

            elif key == "old_legend_clear":

                try:
                    for _tl_attr in ("gauntlets", "collab_gauntlets"):
                        _ga = getattr(sf, _tl_attr)
                        _cnt = _filled = 0
                        _n_stages = max(
                            (len(_ch.stages) for _cs in _ga.chapters for _ch in _cs.chapters if _ch.stages),
                            default=30
                        )
                        for _cs in _ga.chapters:
                            for _ch in _cs.chapters:
                                _ch.chapter_unlock_state = 3
                                if _ch.stages:
                                    for _st in _ch.stages: _st.clear_times = 1
                                    _ch.clear_progress = len(_ch.stages)
                                    _ch.total_stages = len(_ch.stages)
                                    _filled += 1
                                else:
                                    _ch.clear_progress = _n_stages
                                    _ch.total_stages = _n_stages
                            _cnt += 1
                        if hasattr(_ga, "unknown") and _ga.chapters:
                            _ga.unknown = [_ga.get_total_stars(0)] * len(_ga.chapters)
                        logger.info(f"old_legend_clear {_tl_attr}: {_cnt}ch filled={_filled}")
                except Exception as _e:
                    logger.warning(f"old_legend_clear失敗: {_e}")

            elif key == "true_legend_clear":

                try:
                    _clear_chapters(sf, sf.uncanny.chapters, "true_legend_clear", logger)
                except Exception as _e:
                    logger.warning(f"true_legend_clear失敗: {_e}")

            elif key == "zero_legend_clear":
                _clear_chapters(sf, sf.zero_legends, "zero_legend_clear", logger)

            elif key == "makai_clear":
                _clear_chapters(sf, sf.aku, "makai_clear", logger)

            elif key == "event_clear":
                from bcsfe import core as _c
                cleared = []
                for _fn, _lbl in [
                    (_c.game.map.event.EventChapters.edit_sol_chapters,   "sol"),
                    (_c.game.map.event.EventChapters.edit_event_chapters,  "event"),
                    (_c.game.map.event.EventChapters.edit_collab_chapters, "collab"),
                ]:
                    try:
                        _auto_run(_fn, sf, ["10"])
                        cleared.append(_lbl)
                    except: pass
                if cleared:
                    logger.info(f"event_clear: {cleared} 完了")
                else:
                    try:
                        _cnt = 0
                        for _ea in ("event_chapters","sol_chapters","collab_chapters","extra_stages"):
                            _obj = getattr(sf, _ea, None)
                            if _obj is None: continue
                            _lst = getattr(_obj,"chapters",getattr(_obj,"data",_obj))
                            for _ch in _lst:
                                for _ca in ("cleared","clear_count","state"):
                                    try:
                                        _so = getattr(_ch, _ca, None)
                                        if _so is None: continue
                                        try: _so.value = 1
                                        except: setattr(_ch, _ca, 1)
                                        _cnt += 1; break
                                    except: pass
                        logger.info(f"event_clear: 直接 {_cnt}件 完了")
                    except Exception as _e:
                        logger.warning(f"event_clear 全失敗: {_e}")

            elif key == "all_char_unlock":
                try:

                    ERROR_IDS = {
                        155, 182, 285, 320, 339, 353,
                        432, 433, 465, 492, 497, 498, 499, 500,
                        673, 740, 741, 742, 743, 744, 745, 788
                    }
                    unlocked = guide_set = 0

                    try:
                        _all = list(sf.cats.get_all_cats())
                    except Exception:
                        _all = list(sf.cats.cats)
                    _known_ids = set()
                    for _cat in _all:
                        try:
                            _known_ids.add(int(_cat.id.value) if hasattr(_cat.id,"value") else int(_cat.id))
                        except: pass

                    _max_known = max(_known_ids) if _known_ids else 900
                    for _extra_id in range(_max_known + 1, _max_known + 100):
                        if _extra_id in _known_ids: continue
                        try:
                            _extra_cat = sf.cats.get_cat_by_id(_extra_id)
                            if _extra_cat is not None: _all.append(_extra_cat)
                        except: break
                    for _cat in _all:
                        try:
                            _cid = int(_cat.id.value) if hasattr(_cat.id,"value") else int(_cat.id)
                        except: continue
                        if _cid < 0 or _cid in ERROR_IDS: continue
                        try: _cat.unlock(sf); unlocked += 1
                        except: pass
                        for _gattr in ("catguide_collected", "cat_guide_collected", "guide_collected", "guide"):
                            try: setattr(_cat, _gattr, True); guide_set += 1; break
                            except: pass
                    _total = len(_all)
                    logger.info(f"all_char_unlock: {unlocked}体開放 / 図鑑{guide_set}体 (total_cats={_total}, skipped={_total - unlocked})")
                except Exception as e:
                    logger.warning(f"all_char_unlock 失敗: {e}")

            elif key == "error_char_delete":
                try:
                    # 内部IDで指定（表示ID-1）
                    FORCE_DELETE = {
                        155, 182, 285, 320, 339, 353,
                        432, 433, 465, 492, 497, 498, 499, 500,
                        673, 740, 741, 742, 743, 744, 745, 788
                    }
                    cat_list = list(sf.cats.cats)
                    removed = 0
                    removed_ids = []
                    for _cat in cat_list:
                        try: _cid = int(_cat.id) if not hasattr(_cat.id,"value") else int(_cat.id.value)
                        except: continue
                        if _cid not in FORCE_DELETE: continue
                        _ok = False
                        # ① cat.remove()
                        try: _cat.remove(reset=True, save_file=sf); _ok = True
                        except:
                            try: _cat.remove(save_file=sf); _ok = True
                            except: pass
                        # ② unlock=False / locked=True でロック
                        if not _ok:
                            for _la in ("unlocked","is_unlocked","owned"):
                                try: setattr(_cat, _la, False); _ok = True; break
                                except: pass
                        # ③ upgrade level を 0 に、form を 0 に
                        try: _cat.upgrade.base.value = 0
                        except:
                            try: _cat.upgrade.base = 0
                            except: pass
                        try:
                            _fv = getattr(_cat, "current_form", None) or getattr(_cat, "form", None)
                            if _fv is not None:
                                try: _fv.value = 0
                                except: setattr(_cat, "current_form", 0)
                        except: pass
                        removed += 1
                        removed_ids.append(_cid)
                    logger.info(f"error_char_delete: {removed}体処理 IDs={sorted(removed_ids)}")
                except Exception as e:
                    logger.warning(f"error_char_delete 失敗: {e}")

            elif key == "all_char_lv_max":
                try:
                    from bcsfe import core as _c
                    _lv_cnt = 0
                    for cat in sf.cats.cats:
                        try:
                            pu = _c.PowerUpHelper(cat, sf)
                            max_base = pu.get_max_possible_base() - 1
                            max_plus = pu.get_max_possible_plus()
                            # base
                            try: cat.upgrade.base.value = max_base
                            except:
                                try: cat.upgrade.base = max_base
                                except: pass

                            try: cat.upgrade.plus.value = max_plus
                            except:
                                try: cat.upgrade.plus = max_plus
                                except: pass
                            _lv_cnt += 1
                        except: pass
                    logger.info(f"all_char_lv_max: {_lv_cnt}体 完了")
                except Exception as e:
                    logger.warning(f"all_char_lv_max 失敗: {e}")

            elif key == "all_char_max_form":
                try:
                    from bcsfe import core as _c
                    ERROR_IDS_FORM = {
                        155, 182, 285, 320, 339, 353,
                        432, 433, 465, 492, 497, 498, 499, 500,
                        673, 740, 741, 742, 743, 744, 745, 788
                    }
                    _form_cnt = _skip_cnt = _debug_sample = 0
                    for _cat in sf.cats.cats:
                        try:
                            try: _cid = int(_cat.id.value) if hasattr(_cat.id,"value") else int(_cat.id)
                            except: _cid = -1
                            if _cid < 0 or _cid in ERROR_IDS_FORM: _skip_cnt += 1; continue

                            # unlock状態確認 - 未開放はスキップ
                            _unlocked = False
                            for _ua in ("unlocked","is_unlocked","owned"):
                                _uv = getattr(_cat, _ua, None)
                                if _uv is not None:
                                    _unlocked = bool(getattr(_uv,"value",_uv))
                                    break
                            if not _unlocked: _skip_cnt += 1; continue

                            # 形態数取得: current_form の最大値から推定
                            _n_forms = 1
                            for _fa2 in ("forms", "num_forms", "max_form"):
                                try:
                                    _mf = getattr(_cat, _fa2, None)
                                    if _mf is None: continue
                                    _v = len(_mf) if hasattr(_mf,"__len__") else int(getattr(_mf,"value",_mf))
                                    if _v > 1: _n_forms = _v; break
                                except: pass
                            if _n_forms == 1:
                                try:
                                    _fms = _cat.get_forms(sf)
                                    if _fms and len(_fms) > 1: _n_forms = len(_fms)
                                except: pass
                            # cat.idでゲームデータから形態数を取得
                            if _n_forms == 1:
                                try:
                                    import os as _os
                                    # bcsfe の Cat クラス経由でなく、upgrade.base の max から推定
                                    _pu = _c.PowerUpHelper(_cat, sf)
                                    _mxb = _pu.get_max_possible_base()
                                    if _mxb and _mxb > 30: _n_forms = 2  # 最低2形態
                                    if _mxb and _mxb > 50: _n_forms = 3  # 3形態以上
                                except: pass

                            # n_forms=1は取得失敗 → 2(第3形態)をデフォルトにする
                            if _n_forms <= 1: _n_forms = 3
                            _target = _n_forms - 1
                            if _debug_sample < 3:
                                logger.info(f"max_form debug: cat={_cid} n_forms={_n_forms} target={_target}")
                                _debug_sample += 1

                            for _fa in ("current_form","form","cat_form","evolve"):
                                try:
                                    _obj = getattr(_cat, _fa, None)
                                    if _obj is None: continue
                                    try: _obj.value = _target
                                    except: setattr(_cat, _fa, _target)
                                    _form_cnt += 1; break
                                except: pass
                        except: pass
                    logger.info(f"all_char_max_form: {_form_cnt}体 完了 (skip={_skip_cnt})")
                except Exception as e:
                    logger.warning(f"all_char_max_form 失敗: {e}")

            elif key == "all_honnou_max":
                try:
                    _hn_cnt = 0
                    _td = None
                    try: _td = sf.cats.read_talent_data(sf)
                    except: pass
                    # Talentクラスをbcsfeから直接取得
                    _TalentCls = None
                    try:
                        import importlib as _il
                        for _mp, _cn in [
                            ("bcsfe.core.game.catbase.talents","Talent"),
                            ("bcsfe.core.game.catbase.cat","Talent"),
                            ("bcsfe.core","Talent"),
                        ]:
                            try:
                                _mod = _il.import_module(_mp)
                                _TalentCls = getattr(_mod, _cn, None)
                                if _TalentCls: break
                            except: pass
                    except: pass
                    logger.info(f"all_honnou_max debug: TalentCls={_TalentCls}")
                    _none_cnt = _init_cnt = _filled_cnt = 0
                    # cats が少ない（未開放）場合は事前に全開放
                    if len(sf.cats.cats) < 500:
                        try:
                            ERROR_IDS_H = {155,182,285,320,339,353,432,433,465,492,497,498,499,500,673,740,741,742,743,744,745,788}
                            _all2 = list(sf.cats.get_all_cats())
                            for _c2 in _all2:
                                try:
                                    _cid2 = int(_c2.id.value) if hasattr(_c2.id,"value") else int(_c2.id)
                                    if _cid2 < 0 or _cid2 in ERROR_IDS_H: continue
                                    _c2.unlock(sf)
                                except: pass
                            logger.info("all_honnou_max: 事前 all_char_unlock 実行")
                        except: pass
                    _all_cats = list(sf.cats.cats)
                    # talent_data を read_talent_data で取得（cat_editor.py 準拠）
                    _td2 = None
                    try: _td2 = sf.cats.read_talent_data(sf)
                    except: pass
                    # 最初の1匹でTalentコンストラクタを確認
                    _talent_args_ok = None
                    if _TalentCls is not None and _td is not None:
                        for _tc in _all_cats[:20]:
                            _d = _td.get_cat_talents(_tc)
                            if _d is None: continue
                            _, _mlvs, _, _ids2 = _d
                            if not _ids2: continue
                            for _args in [(_ids2[0], _mlvs[0]), (_ids2[0], _mlvs[0], 0), (_ids2[0],), ()]:
                                try:
                                    _nt = _TalentCls(*_args)
                                    if hasattr(_nt, "write"):
                                        _talent_args_ok = _args
                                        break
                                except: pass
                            if _talent_args_ok is not None: break
                    # talent_args=None → _all_cats全体を検索
                    if _talent_args_ok is None and _TalentCls is not None and _td is not None:
                        for _tc2 in _all_cats:
                            try:
                                _d2 = _td.get_cat_talents(_tc2)
                                if _d2 is None: continue
                                _, _mlvs2, _, _ids2 = _d2
                                if not _ids2 or not _mlvs2 or max(_mlvs2) == 0: continue
                                _ti2 = next((i for i, m in enumerate(_mlvs2) if m > 0), 0)
                                for _try_args in [(_ids2[_ti2], _mlvs2[_ti2]), (_ids2[_ti2], _mlvs2[_ti2], 0)]:
                                    try:
                                        _nt = _TalentCls(*_try_args)
                                        if hasattr(_nt, "write"):
                                            _talent_args_ok = _try_args; break
                                    except: pass
                                if _talent_args_ok: break
                            except: pass
                    logger.info(f"all_honnou_max debug: talent_args={_talent_args_ok}")
                    for _cat in _all_cats:
                        _tals = getattr(_cat, "talents", None)
                        if _tals is None: _none_cnt += 1
                        else: _filled_cnt += 1
                        if _td is None: continue
                        try:
                            _data = _td.get_cat_talents(_cat)
                            if _data is None: continue
                            _, _maxlvs, _, _ids = _data
                            if not _ids: continue
                            _ok = False
                            if _tals is None:
                                # talents=None → unlock()でtalentsを初期化させてから再取得
                                try: _cat.unlock(sf)
                                except: pass
                                _tals = getattr(_cat, "talents", None)
                                # まだNoneなら直接Talentリストを生成
                                if _tals is None and _TalentCls is not None and _talent_args_ok is not None:
                                    _new_tals = []
                                    for _ti, _tid_i in enumerate(_ids):
                                        try: _new_tals.append(_TalentCls(_tid_i, _maxlvs[_ti])); 
                                        except:
                                            try: _new_tals.append(_TalentCls(_tid_i, _maxlvs[_ti], 0))
                                            except: pass
                                    if _new_tals:
                                        for _tattr in ("talents", "_talents"):
                                            try: object.__setattr__(_cat, _tattr, _new_tals); break
                                            except: pass
                                        _tals = getattr(_cat, "talents", None)
                                        if _tals: _init_cnt += 1
                                if _tals is not None:
                                    for _ti, _tid_i in enumerate(_ids):
                                        try:
                                            _t = _cat.get_talent_from_id(_tid_i)
                                            if _t: _t.level = _maxlvs[_ti]; _ok = True
                                        except: pass
                            else:
                                for _ti, _tid_f in enumerate(_ids):
                                    try:
                                        _t = _cat.get_talent_from_id(_tid_f)
                                        if _t is not None:
                                            _t.level = _maxlvs[_ti]; _ok = True
                                    except: pass
                            if _ok:
                                _hn_cnt += 1
                        except: pass
                    logger.info(f"all_honnou_max: {_hn_cnt}体完了 (TalentCls={_TalentCls is not None}, td={'OK' if _td else 'None'}, none={_none_cnt}, init={_init_cnt}, filled={_filled_cnt})")
                except Exception as e:
                    logger.warning(f"all_honnou_max 失敗: {e}")
            elif key == "telop_delete":
                try:
                    from bcsfe import core as _c
                    _c.StoryChapters.clear_tutorial(sf)
                    logger.info("telop_delete: 完了")
                except Exception as e:
                    logger.warning(f"telop_delete 失敗: {e}")

            elif key == "slot_max":
                # _auto_run で edit_unlocked_slots に max値を渡す
                try:
                    from bcsfe.cli.edits.basic_items import BasicItems as _BI
                    _auto_run(_BI.edit_unlocked_slots, sf, ["19"])
                    logger.info("slot_max: 19スロット完了")
                except Exception as e1:
                    # フォールバック: sf.lineups 属性を直接スキャン
                    try:
                        _ln = sf.lineups
                        for _a in dir(_ln):
                            if _a.startswith("_"): continue
                            if "slot" in _a.lower() or "unlock" in _a.lower():
                                try: setattr(_ln, _a, 19)
                                except:
                                    try: getattr(_ln, _a).value = 19
                                    except: pass
                        logger.info("slot_max: フォールバック完了")
                    except Exception as e2:
                        logger.warning(f"slot_max 失敗: {e1} / {e2}")

            elif key == "medal_all":
                try:
                    from bcsfe import core as _c
                    try:
                        _auto_run(_c.game.catbase.medals.Medals.edit_medals, sf, ["1"])
                        logger.info("medal_all: CLI 完了")
                    except Exception as _me:
                        logger.warning(f"medal_all CLI失敗: {_me}")
                    _mo = sf.medals
                    _lst1 = getattr(_mo, "medal_data_1", None)
                    if _lst1 is not None:
                        _existing = set()
                        for _v in _lst1:
                            try: _existing.add(int(_v))
                            except: pass
                        _added = 0
                        for _mid in range(128):
                            if _mid not in _existing:
                                try: _lst1.append(_mid); _added += 1
                                except: pass
                        logger.info(f"medal_all: {_added}個追加 完了 (計{len(_lst1)})")
                    else:
                        logger.warning("medal_all: medal_data_1 なし（CLIのみ）")
                except Exception as e:
                    logger.warning(f"medal_all 失敗: {e}")
            elif key == "enemy_book_all":
                try:
                    from bcsfe import core as _c
                    for _i in range(len(sf.enemy_guide)):
                        _c.Enemy(_i).unlock_enemy_guide(sf)
                    logger.info(f"enemy_book_all: {len(sf.enemy_guide)}体完了")
                except Exception as e:
                    logger.warning(f"enemy_book_all 失敗: {e}")

            elif key == "enemy_book_all":
                try:
                    from bcsfe import core as _c
                    for _i in range(len(sf.enemy_guide)):
                        _c.Enemy(_i).unlock_enemy_guide(sf)
                    logger.info(f"enemy_book_all: {len(sf.enemy_guide)}体完了")
                except Exception as e:
                    logger.warning(f"enemy_book_all 失敗: {e}")

            elif key == "user_rank_all":
                # ランクを40000に
                try:
                    try: sf.user_rank = 40000
                    except:
                        try: sf.user_rank.value = 40000
                        except: pass
                    logger.info("user_rank_all: rank=40000 完了")
                except Exception as e:
                    logger.warning(f"user_rank_all rank失敗: {e}")
                # ランクアップセール無効化
                for _ra in ("rank_up_sale_value","rank_sale_value","sale_value"):
                    try:
                        _v = getattr(sf, _ra, None)
                        if _v is None: continue
                        try: _v.value = 0
                        except: setattr(sf, _ra, 0)
                        logger.info(f"user_rank_all: {_ra}=0 セール無効化 完了"); break
                    except: pass
                # 報酬を全受取
                try:
                    _rw = 0
                    for _r in sf.user_rank_rewards.rewards:
                        for _a in ("claimed","received","unlocked"):
                            try:
                                _v = getattr(_r, _a, None)
                                if _v is None: continue
                                try: _v.value = True
                                except: setattr(_r, _a, True)
                                _rw += 1; break
                            except: pass
                    logger.info(f"user_rank_all: 報酬{_rw}件受取完了")
                except Exception as e:
                    logger.warning(f"user_rank_all 報酬失敗: {e}")

            elif key == "playtime_max":

                done = False
                for outer in ("play_time", "officer_pass"):
                    try:
                        obj = getattr(sf, outer, None)
                        if obj is None: continue
                        for atr in ("play_time", "time", "value"):
                            try:
                                sub = getattr(obj, atr, None)
                                if sub is None:
                                    if atr == "value":
                                        try: obj.value = 99999999
                                        except: setattr(sf, outer, 99999999)
                                        done = True
                                    continue
                                try: sub.value = 99999999
                                except: setattr(obj, atr, 99999999)
                                done = True; break
                            except: pass
                        if done: break
                    except: pass
                if not done: sv("play_time", 99999999)

            elif key == "gold_pass":
                try:
                    _auto_run(sf.officer_pass.gold_pass.edit_gold_pass, sf, ["1"])
                except Exception as e:
                    logger.warning(f"gold_pass 失敗: {e}")

            elif key == "facility_max":
                from bcsfe import core as _c
                # CLI
                try:
                    _auto_run(_c.game.catbase.ototo.Ototo.edit_engineers, sf, ["10"])
                    logger.info("facility_max: CLI engineers 完了")
                except: pass
                try:
                    _auto_run(_c.game.catbase.ototo.Ototo.upgrade_cannon, sf, ["0","20","20","20","20"])
                    logger.info("facility_max: CLI cannon 完了")
                except: pass
                # 直接セット
                try:
                    try: sf.ototo.engineers.value = 10
                    except: sf.ototo.engineers = 10
                    logger.info("facility_max: engineers = 10 完了")
                except Exception as e:
                    logger.warning(f"facility_max engineers 失敗: {e}")
                try:
                    _mat_cnt = 0
                    for m in sf.ototo.base_materials.materials:
                        try: m.amount.value = 999; _mat_cnt += 1
                        except:
                            try: m.amount = 999; _mat_cnt += 1
                            except: pass
                    logger.info(f"facility_max: materials {_mat_cnt}個 完了")
                except Exception as e:
                    logger.warning(f"facility_max base_materials 失敗: {e}")
                try:
                    _cannons_list = sf.ototo.cannons.cannons
                    logger.info(f"facility_max cannons debug: count={len(_cannons_list)}, sample_attrs={[a for a in dir(_cannons_list[0]) if not a.startswith('_')][:12] if _cannons_list else []}")
                    # cannons[0] の levels の中身をデバッグ
                    if _cannons_list:
                        try:
                            _lv0 = _cannons_list[0].levels
                            _lv0_type = type(_lv0).__name__
                            _lv0_len = len(_lv0) if hasattr(_lv0, "__len__") else "?"
                            _lv0_item_attrs = [a for a in dir(_lv0[0]) if not a.startswith("_")] if _lv0_len and _lv0_len > 0 else []
                            logger.info(f"cannons levels debug: type={_lv0_type}, len={_lv0_len}, item_attrs={_lv0_item_attrs}")
                        except Exception as _e:
                            logger.info(f"cannons levels debug error: {_e}")
                    # levels は int リスト → edit_cannon_level 経由で設定
                    # cannons.cannons はint(ID)リスト → get_cannon(id) で実オブジェクト取得
                    _can_cnt = 0
                    for _cannon_id in _cannons_list:
                        try:
                            _cannon = sf.ototo.get_cannon(_cannon_id)
                            if _cannon is None: continue
                            lvs = _cannon.levels
                            _lvlen = len(lvs)
                            if _lvlen == 0:
                                try:
                                    _dv = getattr(_cannon, "development", None)
                                    if _dv is not None:
                                        try: _dv.value = 999
                                        except: setattr(_cannon, "development", 999)
                                    _can_cnt += 1; continue
                                except: pass
                            # ゲーム内上限はおそらく10前後
                            _max_lv = 29
                            _ok = False
                            try:
                                _cannon.levels = [_max_lv] * _lvlen
                                _ok = True
                            except: pass
                            if not _ok:
                                try:
                                    for _li in range(_lvlen):
                                        lvs[_li] = _max_lv
                                    _ok = True
                                except: pass
                            if _ok: _can_cnt += 1
                            else: logger.warning(f"cannon[{_cannon_id}] levels set failed")
                        except Exception as _e:
                            logger.warning(f"cannon[{_cannon_id}] error: {_e}")
                    logger.info(f"facility_max: cannons {_can_cnt}基 完了")
                except Exception as e:
                    logger.warning(f"facility_max cannons 失敗: {e}")

            elif key == "gamatoto_max":

                try:
                    obj = sf.gamatoto
 
                    try: obj.xp = 99999999
                    except:
                        try: obj.xp.value = 99999999
                        except: pass
                    logger.info("gamatoto_max: xp = 99999999 セット完了")
                except Exception as e:
                    logger.warning(f"gamatoto_max 失敗: {e}")

            elif key == "gamatoto_legend":
                try:
                    _lst = sf.gamatoto.helpers.helpers
                    _changed = 0
                    # 1体目のhelperの属性をデバッグ表示
                    if _lst:
                        _h0 = _lst[0]
                        _h0_attrs = {a: getattr(_h0, a, "N/A") for a in dir(_h0) if not a.startswith("_") and not callable(getattr(_h0, a, None))}
                        logger.info(f"gamatoto_legend debug: helper attrs={list(_h0_attrs.keys())}, values sample={dict(list(_h0_attrs.items())[:5])}")
                    for _h in _lst:
                        # id = ガマトト助手のキャラID（レジェンドレアID=5はRarityではなくcat_id）
                        # 実際はcat idを直接セット
                        try:
                            _id_obj = _h.id
                            try: _id_obj.value = 5; _changed += 1
                            except: object.__setattr__(_h, "id", 5); _changed += 1
                        except: pass
                    # セット後の値確認
                    _sample_after = {}
                    if _lst:
                        _h0 = _lst[0]
                        for _a in dir(_h0):
                            if not _a.startswith("_") and not callable(getattr(_h0,_a,None)):
                                try: _sample_after[_a] = getattr(_h0, _a)
                                except: pass
                    logger.info(f"gamatoto_legend: {_changed}/{len(_lst)}体 セット完了 after={dict(list(_sample_after.items())[:3])}")
                except Exception as _e1:
                    logger.warning(f"gamatoto_legend 失敗: {_e1}")

            elif key == "ad_free":
                try:
                    from bcsfe import core as _c
                    try:
                        _auto_run(_c.game.catbase.ad_attributes.AdAttributes.edit_ad_attributes, sf, ["1"])
                        logger.info("ad_free: CLI 完了")
                    except: pass
                    try: sf.ad_free = True
                    except:
                        try: sf.ad_free.value = True
                        except: pass
                    # ad_attributes 直接セット
                    for _aattr in ("ad_attributes","ad_attr","ad_free_attributes"):
                        try:
                            _ao = getattr(sf, _aattr, None)
                            if _ao is None: continue
                            for _a in (getattr(_ao, "attributes", None) or [_ao]):
                                for _fa in ("value","is_free","free","ad_free"):
                                    try: setattr(_a, _fa, True); break
                                    except: pass
                        except: pass
                    logger.info("ad_free: 完了")
                except Exception as e:
                    logger.warning(f"ad_free 失敗: {e}")

            elif key == "ototo_max":
                try:
                    _cannons = sf.ototo.cannons.cannons
                    for _ci2, _cannon in enumerate(_cannons):
                        # development を 999 に（オリジナルと同一）
                        for _da in ("development","dev","develop"):
                            try:
                                _dv = getattr(_cannon, _da, None)
                                if _dv is None: continue
                                try: _dv.value = 999
                                except: setattr(_cannon, _da, 999)
                                break
                            except: pass
                        # levels を直接セット
                        try:
                            for _li in range(len(_cannon.levels)):
                                try: _cannon.levels[_li].value = 999
                                except:
                                    try: _cannon.levels[_li] = 999
                                    except: pass
                        except: pass
                    logger.info(f"ototo_max: {len(_cannons)}基 development=999 完了")
                except Exception as e:
                    logger.warning(f"ototo_max 失敗: {e}")
                # 白城化: にゃんこ城ベース(base_form=0)に設定
                try:
                    _ot = sf.ototo
                    _ot_attrs = [a for a in dir(_ot) if not a.startswith("_")]
                    logger.info(f"ototo debug: attrs={_ot_attrs[:15]}")
                    # base_form / castle_type / base / form を試す
                    _shiro_set = False
                    for _ba in ("improve_id", "base_form", "castle_type", "castle_form", "base", "form", "skin"):
                        try:
                            _bv = getattr(_ot, _ba, None)
                            if _bv is None: continue
                            try: _bv.value = 0
                            except: setattr(_ot, _ba, 0)
                            logger.info(f"ototo_max: 白城化 {_ba}=0 完了")
                            _shiro_set = True; break
                        except: pass
                    if not _shiro_set:
                        logger.warning("ototo_max: 白城化 属性不明")
                except Exception as e:
                    logger.warning(f"ototo_max 白城化失敗: {e}")

            elif key == "shrine_max":
                try:
                    cs = sf.cat_shrine
                    # ① edit_catshrine("50") でレベル50
                    try:
                        _auto_run(cs.edit_catshrine, sf, ["50"])
                        logger.info("shrine_max: edit_catshrine(50) 完了")
                    except Exception as _e1:
                        logger.warning(f"shrine_max edit_catshrine 失敗: {_e1}")
                    # ② 直接セット（level/shrine_level/rank を50に）
                    try:
                        for _la in ("level","shrine_level","rank","lv"):
                            _lv = getattr(cs, _la, None)
                            if _lv is None: continue
                            try: _lv.value = 50
                            except: setattr(cs, _la, 50)
                            logger.info(f"shrine_max: {_la}=50 直接セット完了"); break
                    except Exception as _e2:
                        logger.warning(f"shrine_max 直接セット失敗: {_e2}")
                    # ③ xp_offering も大量セット
                    try:
                        try: cs.xp_offering.value = 999999999
                        except: cs.xp_offering = 999999999
                    except: pass
                except Exception as e:
                    logger.warning(f"shrine_max 失敗: {e}")

            applied.append(ITEM_CONFIG[key]["label"])
        except Exception as e:
            logger.warning(f"[apply_edits] {key} 適用失敗: {e}")
    return applied

def run_bcsfe_download(transfer_code: str, confirmation_code: str, cc_str: str):
    from bcsfe import core
    core.core_data.init_data()
    cc_map = {"jp": "jp", "en": "en", "tw": "tw", "kr": "kr"}
    cc = core.CountryCode(cc_map.get(cc_str.lower(), "jp"))
    gv = core.GameVersion(120200)
    server_handler, result = core.ServerHandler.from_codes(
        transfer_code.strip(),
        confirmation_code.strip(),
        cc,
        gv,
        print=False,
        save_backup=False,
    )
    if server_handler is None:
        if result is not None and result.response is not None:
            return None, f"ダウンロード失敗 (HTTP {result.response.status_code})"
        return None, "ダウンロード失敗（コードまたはネット接続を確認）"
    return server_handler, None


def run_bcsfe_download_clone(transfer_code: str, confirmation_code: str, cc_str: str):
    """垢複製用: 元垢を消さずにセーブデータをコピーして新規アカウントとしてアップロード。
    inquiry_codeを新規生成することで元垢のコードを無効化しない。"""
    from bcsfe import core
    import copy as _copy
    core.core_data.init_data()
    cc_map = {"jp": "jp", "en": "en", "tw": "tw", "kr": "kr"}
    cc = core.CountryCode(cc_map.get(cc_str.lower(), "jp"))
    gv = core.GameVersion(120200)
    # 元垢をダウンロード
    server_handler, result = core.ServerHandler.from_codes(
        transfer_code.strip(),
        confirmation_code.strip(),
        cc,
        gv,
        print=False,
        save_backup=False,
    )
    if server_handler is None:
        if result is not None and result.response is not None:
            return None, f"ダウンロード失敗 (HTTP {result.response.status_code})"
        return None, "ダウンロード失敗（コードまたはネット接続を確認）"
    
    try:
        new_inquiry = core.Random.get_hex_string(32)
        save = server_handler.save_file
        for attr in ("inquiry_code", "inquiry", "nyanko_inquiry_code"):
            try:
                obj = getattr(save, attr, None)
                if obj is None: continue
                try: obj.value = new_inquiry
                except: setattr(save, attr, new_inquiry)
                break
            except Exception: pass
    except Exception as e:
        logger.warning(f"inquiry_code生成失敗（元垢が消える可能性あり）: {e}")
    return server_handler, None


# クラスパッチの復元用ストレージ
_class_patch_restore = {}

def _restore_class_patches():
    """no-opパッチしたクラスメソッドを元に戻す"""
    for _cls, _patches in list(_class_patch_restore.items()):
        for _name, _orig in _patches.items():
            try: setattr(_cls, _name, _orig)
            except: pass
    _class_patch_restore.clear()
    # extra safety: Dojo/Enigma/Uncanny のパッチを必ず復元
    try:
        from bcsfe.core.game.map.dojo import Dojo as _DC
        from bcsfe.core.game.map.enigma import Enigma as _EC
        from bcsfe.core.game.map.uncanny import UncannyChapters as _UC
        import inspect as _ins
        for _cls_r in (_DC, _EC, _UC):
            for _mn in ("write", "write_chapters"):
                _m = getattr(_cls_r, _mn, None)
                if _m and (getattr(_m, "__name__", None) == "<lambda>" or "lambda" in str(_ins.getsource(_m) if hasattr(_m, "__code__") else "")):
                    pass  # should be restored above
    except: pass

def run_bcsfe_upload(server_handler):
    _restore_class_patches()  # アップロード前にパッチを復元
    return server_handler.get_codes(upload_managed_items=False)

# =====================
# 実績チャンネルに投稿
# =====================
async def post_jisseki(bot, user: discord.User, items: list, amount: int, guild_id: int = 0, unit: str = "円"):
    ch_id = get_jisseki_channel_id(guild_id)
    if ch_id is None:
        return
    ch = bot.get_channel(ch_id)
    if ch is None:
        return
    import datetime
    now = datetime.datetime.now()
    timestamp_str = now.strftime("%Y/%m %H:%M")
    items_text = "\n".join(f"・{item}" for item in items)
    embed = discord.Embed(title="代行実績", color=0xccff00)
    embed.add_field(
        name="依頼情報",
        value=f"依頼者: {user.mention}\n```利用金額: {amount}{unit}```",
        inline=False
    )
    embed.add_field(
        name="代行内容",
        value=f"```{items_text}```",
        inline=False
    )
    embed.set_footer(text=f"24/h稼働中🔥 | {timestamp_str}")
    # 購入者のアイコンをThumbnailとして設定
    if user.avatar:
        embed.set_thumbnail(url=user.avatar.url)
    await ch.send(embed=embed)

# =====================
# PayPay受取 共通処理
# =====================
async def paypay_receive(interaction: discord.Interaction, link_raw: str, total: int, label: str) -> bool:
    """PayPayリンク受取。成功:True 失敗:False（エラーメッセージも送信済み）"""
    # 無料注文ではPayPay処理を一切しない
    if max(0, int(total or 0)) <= 0:
        return True
    if not PAYPAY_AVAILABLE:
        await interaction.followup.send(embed=discord.Embed(title="❌ PayPay未対応", description="PayPay機能が利用できません。", color=0xff3333), ephemeral=True)
        return False
    admin_id = str(ADMIN_IDS[0])
    user_paypay = load_paypay_data().get(admin_id)
    if not user_paypay:
        await interaction.followup.send(embed=discord.Embed(title="❌ 管理者PayPay未登録", description="管理者のPayPayアカウントが登録されていません。\n管理者に連絡してください。", color=0xff3333), ephemeral=True)
        log_order(interaction.user.id, str(interaction.user), [label], total, "ADMIN_NO_PAYPAY")
        return False
    link_code = link_raw.strip()
    if "pay.paypay.ne.jp/" in link_code:
        link_code = link_code.split("pay.paypay.ne.jp/")[-1].split("?")[0]
    link_info = await paypayu.check_link(link_code)
    if not link_info:
        await interaction.followup.send(embed=discord.Embed(title="❌ リンク無効", description="送金リンクが無効または使用済みです。", color=0xff3333), ephemeral=True)
        log_order(interaction.user.id, str(interaction.user), [label], total, "INVALID_LINK")
        return False
    try:
        link_amount = int(link_info["payload"]["pendingP2PInfo"]["amount"])
        if link_amount < total:
            await interaction.followup.send(embed=discord.Embed(title="❌ 金額不足", description=f"必要: **{total}円** / 受信: **{link_amount}円**", color=0xff3333), ephemeral=True)
            log_order(interaction.user.id, str(interaction.user), [label], total, f"SHORT:{link_amount}")
            return False
    except (KeyError, TypeError, ValueError):
        pass
    result = await paypayu.link_rev(link_code, user_paypay["phone"], user_paypay["password"], user_paypay["uuid"])
    if result == "LOGINERR":
        await interaction.followup.send(embed=discord.Embed(title="❌ PayPayログインエラー", description="`/paypayログイン` で再ログインしてください。", color=0xff3333), ephemeral=True)
        log_order(interaction.user.id, str(interaction.user), [label], total, "LOGIN_ERR")
        return False
    elif result is not True:
        await interaction.followup.send(embed=discord.Embed(title="❌ 受取失敗", description="管理者にお問い合わせください。", color=0xff3333), ephemeral=True)
        log_order(interaction.user.id, str(interaction.user), [label], total, "RECEIVE_FAIL")
        return False
    return True

# =====================
# bcsfe ダウンロード→アップロード 共通処理
# =====================
async def _refund_point_charge(point_charge, reason):
    if not point_charge: return
    try:
        gid, uid, amount = point_charge
        _point_change(gid, uid, int(amount), reason)
    except Exception:
        logger.exception("ポイント返還失敗")

async def bcsfe_chara_process(interaction: discord.Interaction, t_code: str, a_code: str,
                              service_label: str, chara_ids_str: str, total: int, point_charge=None, earn_points: bool = False):
    """指定キャラ系の自動代行処理"""
    import asyncio, functools
    loop = asyncio.get_event_loop()
    try:
        server_handler, err = await loop.run_in_executor(
            None, functools.partial(run_bcsfe_download, t_code, a_code, "jp")
        )
        if server_handler is None:
            await interaction.followup.send(
                embed=discord.Embed(title="❌ ダウンロード失敗",
                                    description=f"{err}\n\n⚠️ **支払いは既に完了しています。管理者にご連絡ください。**",
                                    color=0xff3333),
                ephemeral=True
            )
            log_order(interaction.user.id, str(interaction.user),
                      [f"{service_label}[ID:{chara_ids_str}]"], total, f"DL_FAIL:{err}")
            await _refund_point_charge(point_charge, "指定キャラ代行失敗返還")
            return

        applied = apply_chara_edits(server_handler.save_file, service_label, chara_ids_str)

        codes = await loop.run_in_executor(None, functools.partial(run_bcsfe_upload, server_handler))
        if codes is None:
            await interaction.followup.send(
                embed=discord.Embed(title="❌ アップロード失敗",
                                    description="⚠️ **支払いは既に完了しています。管理者にご連絡ください。**",
                                    color=0xff3333),
                ephemeral=True
            )
            log_order(interaction.user.id, str(interaction.user),
                      [f"{service_label}[ID:{chara_ids_str}]"], total, "UL_FAIL")
            await _refund_point_charge(point_charge, "指定キャラ代行失敗返還")
            return

        transfer_code, confirmation_code = codes
        items_text = "\n".join(f"✅ {i}" for i in applied) or f"{service_label} ID:{chara_ids_str}"
        embed = discord.Embed(title="🎉 代行完了", description="以下の新しい引き継ぎコードでゲームにログインしてください。", color=0x00cc88)
        embed.add_field(name="適用内容", value=items_text, inline=False)
        embed.add_field(name="新しい引き継ぎ情報",
                        value=f"引き継ぎコード: `{transfer_code}`\n認証番号: `{confirmation_code}`",
                        inline=False)
        await interaction.followup.send(embed=embed, ephemeral=True)
        try:
            await interaction.user.send(embed=embed)
        except discord.Forbidden:
            pass
        log_order(interaction.user.id, str(interaction.user),
                  [f"{service_label}[ID:{chara_ids_str}]"], total, "SUCCESS")
        if earn_points and not point_charge and total > 0:
            _point_change(interaction.guild_id or 0, interaction.user.id, int(total)//10, "代行利用10%還元")
        await post_jisseki(interaction.client, interaction.user, applied, total, interaction.guild_id, unit=("pt" if point_charge else "円"))

    except Exception as e:
        logger.error(f"指定キャラ処理エラー: {e}", exc_info=True)
        await interaction.followup.send(
            embed=discord.Embed(title="❌ 予期しないエラー",
                                description=f"管理者にお問い合わせください。\n```{str(e)[:300]}```",
                                color=0xff3333),
            ephemeral=True
        )
        log_order(interaction.user.id, str(interaction.user),
                  [f"{service_label}[ID:{chara_ids_str}]"], total, f"ERROR:{e}")
        await _refund_point_charge(point_charge, "指定キャラ代行失敗返還")


async def bcsfe_process(interaction: discord.Interaction, t_code: str, a_code: str,
                        item_keys: list, label_list: list, total: int, no_edit: bool = False, is_clone: bool = False, point_charge=None, earn_points: bool = False):
    loop = asyncio.get_event_loop()
    try:
        dl_func = run_bcsfe_download_clone if is_clone else run_bcsfe_download
        server_handler, err = await loop.run_in_executor(None, functools.partial(dl_func, t_code, a_code, "jp"))
        if server_handler is None:
            await interaction.followup.send(embed=discord.Embed(title="❌ ダウンロード失敗", description=f"{err}\n\n⚠️ **支払いは既に完了しています。管理者にご連絡ください。**", color=0xff3333), ephemeral=True)
            log_order(interaction.user.id, str(interaction.user), label_list, 0, f"DL_FAIL:{err}")
            await _refund_point_charge(point_charge, "代行失敗返還")
            return
        if not no_edit:
            # 「指定個数」はmain_bot(3).pyと同じbackendキーへ変換して
            # apply_daiko_segment()に渡す。apply_edits()側の推測書き換えではなく、
            # 実際の新規垢作成/代行処理と同じ経路を使う。
            custom_selected = []
            custom_amounts = {k: 0 for k in CUSTOM_KEYS}
            custom_kind_to_backend = {
                "catfood": "custom_catfood", "xp": "custom_xp", "np": "custom_np",
                "normal_tickets": "custom_normal_tickets", "rare_tickets": "custom_rare_tickets",
                "platinum_tickets": "custom_platinum_tickets", "legend_tickets": "custom_legend_tickets",
                "leadership": "custom_leadership", "battle_items": "custom_battle_items",
                "catamins": "custom_catamins", "catseyes": "custom_catseyes",
                "base_materials": "custom_base_materials", "matatabi": "custom_matatabi",
                "talent_orbs": "custom_talent_orbs", "base_upgrades": "custom_base_upgrades",
                "event_tickets": "custom_event_tickets",
            }
            normal_keys = []
            for key in (item_keys or []):
                parsed = parse_custom_amount_key(key)
                if parsed:
                    kind, amount = parsed
                    backend_key = custom_kind_to_backend.get(kind)
                    if backend_key:
                        custom_selected.append(backend_key)
                        custom_amounts[backend_key] = amount
                    continue
                normal_keys.append(key)

            applied = []
            if custom_selected:
                applied.extend(apply_daiko_segment(
                    server_handler.save_file,
                    list(dict.fromkeys(custom_selected)),
                    [],
                    custom_amounts,
                ))
            if normal_keys:
                applied.extend(apply_edits(server_handler.save_file, normal_keys))
        else:
            applied = label_list
        codes = await loop.run_in_executor(None, functools.partial(run_bcsfe_upload, server_handler))
        if codes is None:
            await interaction.followup.send(embed=discord.Embed(title="❌ アップロード失敗", description="⚠️ **支払いは既に完了しています。管理者にご連絡ください。**", color=0xff3333), ephemeral=True)
            log_order(interaction.user.id, str(interaction.user), label_list, 0, "UL_FAIL")
            await _refund_point_charge(point_charge, "代行失敗返還")
            return
        transfer_code, confirmation_code = codes
        items_text = "\n".join(f"✅ {i}" for i in applied) or "なし"
        embed = discord.Embed(title="🎉 代行完了", description="以下の新しい引き継ぎコードでゲームにログインしてください。", color=0x00cc88)
        embed.add_field(name="適用内容", value=items_text, inline=False)
        embed.add_field(name="新しい引き継ぎ情報", value=f"引き継ぎコード: `{transfer_code}`\n認証番号: `{confirmation_code}`", inline=False)
        await interaction.followup.send(embed=embed, ephemeral=True)
        try:
            await interaction.user.send(embed=embed)
        except discord.Forbidden:
            pass
        log_order(interaction.user.id, str(interaction.user), label_list, total, "SUCCESS")
        if earn_points and not point_charge and total > 0:
            _point_change(interaction.guild_id or 0, interaction.user.id, int(total)//10, "代行利用10%還元")
        await post_jisseki(interaction.client, interaction.user, applied, total, interaction.guild_id, unit=("pt" if point_charge else "円"))
    except ImportError:
        await interaction.followup.send("bcsfe がインストールされていません。管理者にお問い合わせください。", ephemeral=True)
    except Exception as e:
        logger.error(f"代行処理エラー: {e}", exc_info=True)
        await interaction.followup.send(embed=discord.Embed(title="❌ 予期しないエラー", description=f"管理者にお問い合わせください。\n```{str(e)[:300]}```", color=0xff3333), ephemeral=True)
        log_order(interaction.user.id, str(interaction.user), label_list, 0, f"ERROR:{e}")
        await _refund_point_charge(point_charge, "代行失敗返還")


# =====================
# 垢複製 / 全適応 / 復旧 パネル
# =====================

class ServiceModal(ui.Modal, title="情報入力"):
    t_code      = ui.TextInput(label="引き継ぎコード (Transfer Code)", placeholder="例: ABCDEF1234567890", required=True, style=discord.TextStyle.short)
    a_code      = ui.TextInput(label="認証番号 (Confirmation Code)", placeholder="例: 1234", required=True, max_length=10, style=discord.TextStyle.short)

    def __init__(self, service_label: str, total: int, item_keys: list = None, no_edit: bool = False):
        super().__init__(title=f"{service_label} 情報入力", timeout=300)
        self.service_label = service_label
        self.total = max(0, int(total or 0))
        if self.total > 0:
            self.paypay_link = ui.TextInput(label="PayPay 送金リンク", placeholder="https://pay.paypay.ne.jp/xxxx", required=True)
            self.add_item(self.paypay_link)
        self.item_keys = item_keys or []
        self.no_edit = no_edit

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        await interaction.followup.send(embed=discord.Embed(
            title="⏳ 処理中...",
            description="セーブデータ取得中です。" if self.total == 0 else "PayPay送金の確認とセーブデータ取得中です。",
            color=0xffaa00
        ), ephemeral=True)
        if self.total > 0:
            ok = await paypay_receive(interaction, self.paypay_link.value, self.total, self.service_label)
            if not ok:
                return
        log_order(interaction.user.id, str(interaction.user), [self.service_label], self.total, "PAID" if self.total else "FREE")
        await bcsfe_process(interaction, self.t_code.value, self.a_code.value, self.item_keys, [self.service_label], self.total, no_edit=self.no_edit, is_clone=(self.service_label == "垢複製"), earn_points=True)


# =====================
# VIP / アカウントパネル
# vip.html のWeb依存部分をDiscord UIへ移植
# =====================

# vip.html で定義されている項目のうち、現在のmain_bot.pyの
# apply_edits / bcsfe_process で確実に処理できるものをDiscord側へ統合。
VIP_OPTION_MAP = {
    "main_story_clear": "main_clear",
    "zombie_clear": "zombie_clear",
    "aku_clear": "makai_clear",
    "legend_clear": "old_legend_clear",
    "true_legend_clear": "true_legend_clear",
    "zero_legend_clear": "zero_legend_clear",
    "all_stage_clear": "event_clear",
    "gamatoto_max": "gamatoto_max",
    "gamatoto_helpers": "gamatoto_legend",
    "ototo_max": "ototo_max",
    "cat_shrine_max": "shrine_max",
    "base_upgrades_max": "facility_max",
    "gold_membership": "gold_pass",
    "slots_max": "slot_max",
    "medals_all": "medal_all",
    "unlock_enemy_guide": "enemy_book_all",
    "user_rank_rewards_claimed": "user_rank_all",
    "add_playtime_720h": "playtime_max",
    "unlock_all_cats": "all_char_unlock",
    "max_all_cats": "all_char_lv_max",
    "true_form_all": "all_char_max_form",
    "talents_all": "all_honnou_max",
    "remove_error_cats": "error_char_delete",
    "telop_delete": "telop_delete",
    "ad_free": "ad_free",
    "ototo_detailed": "ototo_max",
    "future_score_detailed": "future_score",
    "future_score_individual": "future_score",
    "future_score_random": "future_score",
    "dojo_score_detailed": "dojo_score",
    "legend_detail": "legend_detail",
    "ototo_detail": "ototo_detail",
    "lineup_custom": "lineup_custom",
    "labyrinth_detail": "labyrinth_detail",
    "event_detail": "event_detail",
    "main_stage_detail": "main_stage_detail",
    "special_stage_detail": "special_stage_detail",
    "facility_detail": "facility_detail",
    "talent_orb_detail": "talent_orb_detail",
    "event_ticket_detail": "event_ticket_detail",
    "skip_tutorial": "skip_tutorial",
    "hide_rank_up": "hide_rank_up",
    "user_rank_rewards_unclaimed": "user_rank_rewards_unclaimed",
    "catguide_rewards_claimed": "catguide_rewards_claimed",
    "catguide_rewards_unclaimed": "catguide_rewards_unclaimed",
    "cat_scratcher_reset": "cat_scratcher_reset",
    "labyrinth_medals": "dungeon_medal_99",
    "all_missions_clear": "all_missions_clear",
    "max_all_cats_plus": "all_char_lv_max_plus",
    "talents_disable_all": "talents_disable_all",
}

VIP_CUSTOM_OPTIONS = [
    ("猫缶", "catfood"), ("XP", "xp"), ("NP", "np"),
    ("にゃんこチケット", "normal_tickets"), ("レアチケット", "rare_tickets"),
    ("プラチナチケット", "platinum_tickets"), ("レジェンドチケット", "legend_tickets"),
    ("リーダーシップ", "leadership"), ("バトルアイテム全種", "battle_items"),
    ("ネコビタン全種", "catamins"), ("キャッツアイ全種", "catseyes"),
    ("城素材全種", "base_materials"), ("マタタビ全種", "matatabi"),
    ("本能玉全種", "talent_orbs"), ("イベントチケット全種", "event_tickets"),
    ("全施設", "base_upgrades"), ("プレイ時間（時間）", "playtime"),
]

class VipCustomAmountModal(ui.Modal, title="指定個数を入力"):
    amount = ui.TextInput(label="個数 / レベル / 時間", placeholder="例: 1000", required=True, min_length=1, max_length=9)

    def __init__(self, kind: str, label: str, payment_mode: str = "yen"):
        super().__init__(timeout=300)
        self.kind = kind
        self.item_label = label
        self.payment_mode = payment_mode

    async def on_submit(self, interaction: discord.Interaction):
        try:
            amount = int(self.amount.value.replace(",", "").strip())
            if amount < 0 or amount > 9999999:
                raise ValueError
        except ValueError:
            await interaction.response.send_message("❌ 0〜9,999,999の範囲で整数を入力してください。", ephemeral=True)
            return
        key = make_custom_amount_key(self.kind, amount)
        # CUSTOM_AMOUNT_BASE[self.kind] は「基準価格の整数」なので、
        # get_price() に渡すと int.startswith() で落ちる。
        # 指定個数は生成した custom_amount|種類|数量 キーで価格を取得する。
        price = get_point_price(key, interaction.guild_id or 0) if self.payment_mode == "points" else get_price(key, interaction.guild_id or 0)
        unit = "pt" if self.payment_mode == "points" else "円"
        await interaction.response.send_message(
            embed=discord.Embed(
                title="🛒 指定個数 注文確認",
                description=f"・{custom_amount_label(self.kind, amount)}\n・価格: **{price}{unit}**",
                color=0xf5c542 if self.payment_mode == "points" else 0x38bdf8,
            ),
            view=VipConfirmView([key], payment_mode=self.payment_mode),
            ephemeral=True,
        )

class VipCustomSelect(ui.Select):
    def __init__(self, payment_mode: str = "yen"):
        self.payment_mode = payment_mode
        super().__init__(
            placeholder="④ 指定個数（1から自由に入力）",
            min_values=1, max_values=1,
            options=[discord.SelectOption(label=label, value=kind, description="個数を自由に指定") for label, kind in VIP_CUSTOM_OPTIONS],
            row=4,
            custom_id="vip_custom_amount_select",
        )

    async def callback(self, interaction: discord.Interaction):
        kind = self.values[0]
        label = dict((kind, label) for label, kind in VIP_CUSTOM_OPTIONS)[kind]
        await interaction.response.send_modal(VipCustomAmountModal(kind, label, payment_mode=self.payment_mode))

# vip.html の「新規アカウント作成」欄をDiscordへ移植。
NEW_ACCOUNT_GROUPS = {
    "アイテム・ステージ": [
        ("メインステージ(お宝金＆クリア)", "main_story_clear"),
        ("メインゾンビステージ全クリア", "zombie_clear"),
        ("魔界編全クリア", "aku_clear"),
        ("レジェンド全クリア", "legend_clear"),
        ("真レジェンド全クリア", "true_legend_clear"),
        ("零レジェンド全クリア", "zero_legend_clear"),
        ("イベントステージ全クリア", "all_stage_clear"),
        ("全ミッションクリア（全種類）", "all_missions_clear"),
        ("地底迷宮 勲章", "labyrinth_medals"),
        ("レジェンドマップ詳細指定 ★", "legend_detail"),
        ("イベントステージ詳細指定 ★", "event_detail"),
        ("メイン章・ステージ個別指定 ★", "main_stage_detail"),
        ("ゾンビ・魔界編詳細指定 ★", "special_stage_detail"),
        ("未来編 採点スコア指定 ★", "future_score_detailed"),
        ("未来編スコア個別指定 ★", "future_score_individual"),
        ("未来編スコアランダム ★", "future_score_random"),
        ("道場スコア指定 ★", "dojo_score_detailed"),
    ],
    "システム・ガマトト": [
        ("ガマトトLv.Max", "gamatoto_max"),
        ("ガマトト助手全レジェンド化", "gamatoto_helpers"),
        ("オトート全城強化Lv.Max", "ototo_max"),
        ("オトート・城強化 詳細指定 ★", "ototo_detail"),
        ("施設ごとのレベル指定 ★", "facility_detail"),
        ("本能玉名 → ランク 個別選択 ★", "talent_orb_detail"),
        ("イベントチケット 種類別選択 ★", "event_ticket_detail"),
        ("にゃんこ神社Lv.Max", "cat_shrine_max"),
        ("全施設 Lv.Max", "base_upgrades_max"),
        ("ゴールド会員化", "gold_membership"),
        ("編成スロット数最大化", "slots_max"),
        ("にゃんこメダル全解放", "medals_all"),
        ("チュートリアルスキップ", "skip_tutorial"),
        ("ランクアップポップアップ非表示", "hide_rank_up"),
        ("ユーザーランク報酬全受取化", "user_rank_rewards_claimed"),
        ("ユーザーランク報酬全未受取化", "user_rank_rewards_unclaimed"),
        ("猫図鑑報酬全受取化", "catguide_rewards_claimed"),
        ("猫図鑑報酬全未受取化", "catguide_rewards_unclaimed"),
        ("スクラッチ未実施化（引き直し）", "cat_scratcher_reset"),
        ("地底迷宮詳細指定 ★", "labyrinth_detail"),
        ("敵キャラ図鑑全解放", "unlock_enemy_guide"),
        ("プレイ時間 +720時間", "add_playtime_720h"),
        ("開放テロップ削除", "telop_delete"),
        ("広告非表示", "ad_free"),
    ],
    "キャラクター": [
        ("全キャラ解放", "unlock_all_cats"),
        ("全キャラLv.Max+", "max_all_cats_plus"),
        ("全キャラLv.Max", "max_all_cats"),
        ("全キャラ最大形態化", "true_form_all"),
        ("全キャラ本能解放", "talents_all"),
        ("全キャラ本能無効", "talents_disable_all"),
        ("エラーキャラ削除", "remove_error_cats"),
        ("編成キャラ個別設定", "lineup_custom"),
    ],
}

# 通常VIPパネルは従来項目を維持。新規垢パネルでは固定リソースを表示しない。
VIP_GROUPS = {
    "リソース・チケット・ステージ系": [
        ("メインステージ全クリア", "main_story_clear"), ("ゾンビステージ全クリア", "zombie_clear"),
        ("魔界編全クリア", "aku_clear"), ("レジェンド全クリア", "legend_clear"),
        ("真レジェンド全クリア", "true_legend_clear"), ("零レジェンド全クリア", "zero_legend_clear"),
        ("イベントステージ全クリア", "all_stage_clear"), ("全ミッションクリア（全種類）", "all_missions_clear"),
        ("地底迷宮 勲章", "labyrinth_medals"), ("レジェンドマップ詳細指定 ★", "legend_detail"),
        ("イベントステージ詳細指定 ★", "event_detail"), ("メイン章・ステージ個別指定 ★", "main_stage_detail"),
        ("ゾンビ・魔界編詳細指定 ★", "special_stage_detail"), ("未来編 採点スコア指定 ★", "future_score_detailed"),
        ("未来編スコア個別指定 ★", "future_score_individual"), ("未来編スコアランダム ★", "future_score_random"),
        ("道場スコア指定 ★", "dojo_score_detailed"),
    ],
    "キャラ・施設・その他系①": [
        ("ガマトトLv.Max", "gamatoto_max"), ("ガマトト助手全レジェンド化", "gamatoto_helpers"),
        ("オトート全城強化Lv.Max", "ototo_max"), ("オトート詳細", "ototo_detail"),
        ("施設ごとのレベル指定 ★", "facility_detail"), ("本能玉名 → ランク 個別選択 ★", "talent_orb_detail"),
        ("イベントチケット 種類別選択 ★", "event_ticket_detail"),
        ("にゃんこ神社Lv.Max", "cat_shrine_max"), ("全施設Lv.Max", "base_upgrades_max"),
        ("ゴールド会員化", "gold_membership"), ("編成スロット最大化", "slots_max"),
        ("にゃんこメダル全解放", "medals_all"), ("地底迷宮詳細指定 ★", "labyrinth_detail"), ("敵キャラ図鑑全解放", "unlock_enemy_guide"),
        ("チュートリアルスキップ", "skip_tutorial"), ("ランクアップポップアップ非表示", "hide_rank_up"),
        ("ユーザーランク報酬全受取", "user_rank_rewards_claimed"), ("ユーザーランク報酬全未受取化", "user_rank_rewards_unclaimed"),
        ("猫図鑑報酬全受取化", "catguide_rewards_claimed"), ("猫図鑑報酬全未受取化", "catguide_rewards_unclaimed"),
        ("スクラッチ未実施化（引き直し）", "cat_scratcher_reset"), ("プレイ時間 +720時間", "add_playtime_720h"),
        ("開放テロップ削除", "telop_delete"), ("広告非表示", "ad_free"),
        ("全キャラ解放", "unlock_all_cats"), ("全キャラLv.Max+", "max_all_cats_plus"),
    ],
    "キャラ・施設・その他系②": [
        ("全キャラLv.Max", "max_all_cats"), ("全キャラ最大形態化", "true_form_all"),
        ("全キャラ本能解放", "talents_all"), ("全キャラ本能無効", "talents_disable_all"),
        ("エラーキャラ削除", "remove_error_cats"), ("編成キャラ個別設定（10枠）", "lineup_custom"),
    ],
}

# ---- 詳細指定UI（vip.htmlの詳細カードをDiscord向けに分割） ----
class DojoScoreModal(ui.Modal):
    def __init__(self,parent_view=None):
        super().__init__(title="道場スコア指定",timeout=300); self.parent_view=parent_view
        self.score=ui.TextInput(label="入門の間スコア",placeholder="例: 381919",default="381919",required=True,max_length=10); self.add_item(self.score)
    async def on_submit(self,interaction):
        try: score=int(self.score.value); assert 0<=score<=2147483647
        except Exception:
            await interaction.response.send_message("❌ 0〜2,147,483,647で指定してください。",ephemeral=True); return
        key=f"dojo_score|{score}"
        await _detail_key_to_parent(interaction,key,f"道場・入門の間スコア {score:,}",self.parent_view)


async def _stage_metadata():
    """vip.html/main13.py と同じ最新ステージメタデータをDiscord UIから取得する。"""
    loop = asyncio.get_running_loop()
    return await loop.run_in_executor(None, get_legend_metadata)


async def _send_detail_key(interaction, key, label, parent_view=None):
    await _detail_key_to_parent(interaction, key, label, parent_view)


class _PagerButton(ui.Button):
    def __init__(self, owner, direction):
        self.owner = owner
        self.direction = direction
        super().__init__(
            label="◀ 前へ" if direction < 0 else "次へ ▶",
            style=discord.ButtonStyle.secondary,
            row=4,
        )

    async def callback(self, interaction):
        total = len(getattr(self.owner, "maps", []))
        max_page = max(0, (total - 1) // 25)
        self.owner.page = max(0, min(max_page, self.owner.page + self.direction))
        self.owner.refresh()
        await interaction.response.edit_message(view=self.owner)


class _StagePagerButton(ui.Button):
    def __init__(self, owner, direction, row=4):
        self.owner = owner
        self.direction = direction
        super().__init__(
            label="◀ ステージ前へ" if direction < 0 else "ステージ次へ ▶",
            style=discord.ButtonStyle.secondary,
            row=row,
        )

    async def callback(self, interaction):
        if hasattr(self.owner, "stage_options"):
            total = len(self.owner.stage_options())
        elif hasattr(self.owner, "selected_map_objects"):
            total = sum(len(m.get("stages", [])) for m in self.owner.selected_map_objects())
        elif hasattr(self.owner, "maps") and hasattr(self.owner, "selected_maps"):
            total = sum(len(m.get("stages", [])) for m in self.owner.maps if int(m.get("id", -1)) in self.owner.selected_maps)
        else:
            total = 0
        max_page = max(0, (total - 1) // 25)
        self.owner.stage_page = max(0, min(max_page, self.owner.stage_page + self.direction))
        self.owner.refresh()
        await interaction.response.edit_message(view=self.owner)


class LegendDetailView(ui.View):
    """シリーズ→マップ一覧(複数)→冠→ステージ一覧(複数)。"""
    def __init__(self, parent_view=None):
        super().__init__(timeout=300)
        self.parent_view = parent_view
        self.series = "legend"
        self.maps = []
        self.selected_maps = set()
        self.crown = 1
        self.selected_stages = set()
        self.page = 0
        self.stage_page = 0
        self.loaded = False
        self.add_item(LegendSeriesSelect(self))

    async def load(self):
        try:
            metadata = await _stage_metadata()
            self.maps = list(metadata.get(self.series, {}).get("maps", []))
            self.loaded = True
        except Exception as e:
            self.maps = []
            self.loaded = False
            self.load_error = str(e)

    def refresh(self):
        for item in list(self.children):
            if not isinstance(item, LegendSeriesSelect):
                self.remove_item(item)
        self.add_item(LegendMapSelect(self))
        self.add_item(LegendCrownSelect(self))
        self.add_item(LegendStageSelect(self))
        self.add_item(LegendFinishButton(self))
        if len(self.maps) > 25:
            self.add_item(_PagerButton(self, -1))
            self.add_item(_PagerButton(self, 1))
        if len(self.stage_options()) > 25:
            self.add_item(_StagePagerButton(self, -1))
            self.add_item(_StagePagerButton(self, 1))

    async def initialize(self, interaction):
        await self.load()
        self.refresh()
        if not self.loaded:
            await interaction.response.send_message(
                "❌ ステージ一覧の取得に失敗しました。少し待ってからもう一度開いてください。",
                ephemeral=True,
            )
            return
        await interaction.response.send_message(
            embed=discord.Embed(
                title="📚 レジェンドマップ詳細指定",
                description="シリーズを1つ選択 → マップ一覧は複数選択 → 冠は1〜4 → ステージ一覧を複数選択してください。",
                color=0x38bdf8,
            ),
            view=self,
            ephemeral=True,
        )

    async def change_series(self, series):
        self.series = series
        self.selected_maps.clear()
        self.selected_stages.clear()
        self.page = 0
        self.stage_page = 0
        try:
            metadata = await _stage_metadata()
            self.maps = list(metadata.get(series, {}).get("maps", []))
        except Exception:
            self.maps = []
        self.refresh()

    def selected_map_objects(self):
        return [m for m in self.maps if int(m.get("id", -1)) in self.selected_maps]

    def stage_options(self):
        # 選択された全マップのステージをまとめる。同じstage_idはマップ別に区別する。
        rows = []
        for m in self.selected_map_objects():
            mid = int(m["id"])
            for sid, name in enumerate(m.get("stages", [])):
                rows.append((f"{m.get('name', f'マップ{mid+1}')[:28]}｜{sid+1}. {str(name)[:60]}",
                             f"{mid}:{sid}"))
        return rows

    def build_key(self):
        payload = {self.series: {}}
        for mid in sorted(self.selected_maps):
            m = next((x for x in self.maps if int(x["id"]) == mid), None)
            if not m:
                continue

            # ステージを1つも選択していない場合は、選択したマップの全ステージを適用。
            selected_for_map = sorted({sid for smid, sid in self.selected_stages if smid == mid})
            if not self.selected_stages:
                selected_for_map = list(range(len(m.get("stages", []))))

            if selected_for_map:
                payload[self.series][str(mid)] = {str(self.crown - 1): selected_for_map}
        return payload


class LegendSeriesSelect(ui.Select):
    def __init__(self, owner):
        self.owner = owner
        super().__init__(
            placeholder="シリーズを選択（1つだけ）",
            min_values=1, max_values=1, row=0,
            options=[
                discord.SelectOption(label="旧レジェンド", value="legend"),
                discord.SelectOption(label="真レジェンド", value="true_legend"),
                discord.SelectOption(label="零レジェンド", value="zero_legend"),
            ],
        )

    async def callback(self, interaction):
        await self.owner.change_series(self.values[0])
        await interaction.response.edit_message(view=self.owner)


class LegendMapSelect(ui.Select):
    def __init__(self, owner):
        self.owner = owner
        page_size = 25
        start = owner.page * page_size
        rows = owner.maps[start:start + page_size]
        options = [
            discord.SelectOption(
                label=f"{int(m['id'])+1}. {str(m.get('name',''))[:90]}",
                value=str(m["id"]),
                default=int(m["id"]) in owner.selected_maps,
            )
            for m in rows
        ] or [discord.SelectOption(label="マップなし", value="none")]
        super().__init__(
            placeholder="マップ一覧（複数選択可）",
            min_values=1, max_values=min(len(options), 25),
            options=options, row=1,
        )

    async def callback(self, interaction):
        self.owner.selected_maps.update(int(v) for v in self.values if v != "none")
        # マップ変更時は、そのマップに存在しないステージ選択を除外。
        valid_pairs = {(int(m["id"]), sid)
                       for m in self.owner.selected_map_objects()
                       for sid in range(len(m.get("stages", [])))}
        self.owner.selected_stages.intersection_update(valid_pairs)
        self.owner.stage_page = 0
        self.owner.refresh()
        await interaction.response.edit_message(view=self.owner)


class LegendCrownSelect(ui.Select):
    def __init__(self, owner):
        self.owner = owner
        super().__init__(
            placeholder=f"冠を選択（現在 {owner.crown}）",
            min_values=1, max_values=1, row=2,
            options=[discord.SelectOption(label=f"{i}冠", value=str(i), default=i == owner.crown) for i in range(1, 5)],
        )

    async def callback(self, interaction):
        self.owner.crown = int(self.values[0])
        await interaction.response.edit_message(view=self.owner)


class LegendStageSelect(ui.Select):
    def __init__(self, owner):
        self.owner = owner
        rows = owner.stage_options()
        start = owner.stage_page * 25
        page_rows = rows[start:start + 25]
        options = [
            discord.SelectOption(label=label[:100], value=value,
                                 default=(tuple(map(int, value.split(":"))) in owner.selected_stages))
            for label, value in page_rows
        ] or [discord.SelectOption(label="先にマップを選択してください", value="none")]
        super().__init__(
            placeholder="ステージ一覧（複数選択可）",
            min_values=1, max_values=min(len(options), 25),
            options=options, row=3,
        )

    async def callback(self, interaction):
        self.owner.selected_stages.update(
            tuple(map(int, v.split(":"))) for v in self.values if v != "none"
        )
        self.owner.refresh()
        await interaction.response.edit_message(view=self.owner)


class LegendFinishButton(ui.Button):
    def __init__(self, owner):
        self.owner = owner
        super().__init__(label="✅ この内容を追加", style=discord.ButtonStyle.success, row=4)

    async def callback(self, interaction):
        if not self.owner.selected_maps:
            await interaction.response.send_message("❌ マップ一覧からマップを選択してください。", ephemeral=True)
            return
        # ステージ一覧を何も選択していない場合は、選択したマップの全ステージを適用します。
        payload = self.owner.build_key()
        if not any(payload[self.owner.series].values()):
            await interaction.response.send_message("❌ 選択したマップにステージがありません。", ephemeral=True)
            return
        key = f"legend_detail|{json.dumps(payload, ensure_ascii=False, separators=(',', ':'))}"
        label = f"{dict([('legend','旧レジェンド'),('true_legend','真レジェンド'),('zero_legend','零レジェンド')])[self.owner.series]} 詳細指定"
        await _send_detail_key(interaction, key, label, self.owner.parent_view)


class LegendDetailModal:
    """旧UIとの互換名。実際にはSelectベースのLegendDetailViewを開く。"""
    def __init__(self, parent_view=None):
        self.parent_view = parent_view

    async def open(self, interaction):
        view = LegendDetailView(self.parent_view)
        await view.initialize(interaction)


class OtotoDetailModal:
    """オトート・城強化をWeb版と同じ名前＋部位レベル指定UIで設定する。"""
    def __init__(self, parent_view=None):
        self.parent_view = parent_view

    async def open(self, interaction):
        try:
            metadata = await asyncio.to_thread(get_ototo_metadata)
            cannons = metadata.get("cannons", [])
        except Exception as e:
            logger.exception("ototo metadata load failed")
            await interaction.response.send_message(
                "❌ オトート・城強化データの取得に失敗しました。", ephemeral=True
            )
            return

        view = OtotoDetailView(self.parent_view, cannons)
        await interaction.response.send_message(
            embed=view.make_embed(), view=view, ephemeral=True
        )


class OtotoDetailView(ui.View):
    """城を複数追加でき、各部位の全レベルをSelectで指定できるUI。"""
    def __init__(self, parent_view=None, cannons=None):
        super().__init__(timeout=300)
        self.parent_view = parent_view
        self.cannons = cannons or []
        self.page = 0
        self.selected_id = str(self.cannons[0]["id"]) if self.cannons else None
        self.selected_parts = {}
        self.active_part_id = None
        self.level_page = 0
        self.settings = {}
        cannon = self.current()
        if cannon and cannon.get("parts"):
            self.active_part_id = str(cannon["parts"][0]["id"])
        self.refresh()

    @property
    def max_page(self):
        return max(0, (len(self.cannons) - 1) // 25)

    def current(self):
        try:
            cid = int(self.selected_id)
        except (TypeError, ValueError):
            return None
        return next((c for c in self.cannons if int(c.get("id", -1)) == cid), None)

    def active_part(self):
        cannon = self.current()
        if not cannon:
            return None
        return next((p for p in cannon.get("parts", []) if str(p.get("id")) == str(self.active_part_id)), None)

    def _current_level(self, cannon, part):
        return int(self.selected_parts.get(str(cannon["id"]), {}).get(
            str(part["id"]), part.get("max_level", 0)))

    def make_embed(self):
        cannon = self.current()
        if not cannon:
            return discord.Embed(title="🏰 オトート・城強化 詳細指定", description="設定できる城強化データがありません。", color=0x38bdf8)
        lines = []
        for part in cannon.get("parts", []):
            lv = self._current_level(cannon, part)
            lines.append(f"**{part['name']}**：Lv.{lv}（{part.get('min_level', 0)}〜{part.get('max_level', 0)}）")
        saved = []
        for cid, setting in self.settings.items():
            item = next((c for c in self.cannons if str(c.get('id')) == str(cid)), None)
            saved.append(f"・{item.get('name', '城強化 #' + str(cid)) if item else '城強化 #' + str(cid)}")
        return discord.Embed(
            title="🏰 オトート・城強化 詳細指定",
            description=(f"城：**{cannon.get('name', '城強化 #' + str(cannon.get('id')))}**\n"
                         f"城一覧ページ：{self.page + 1}/{self.max_page + 1}\n\n" + "\n".join(lines) +
                         "\n\n**追加済みの城**\n" + ("\n".join(saved) if saved else "まだありません") +
                         "\n\n部位を選び、レベル帯→正確なLvを選択してください。"), color=0x38bdf8)

    def refresh(self):
        self.clear_items()
        chunk = self.cannons[self.page * 25:(self.page + 1) * 25]
        if chunk:
            self.add_item(_DetailChoiceSelect(self, "城強化を選択", [
                discord.SelectOption(label=str(c.get("name", f"城強化 #{c.get('id')}"))[:100], value=str(c.get("id")),
                                     description=f"ID {c.get('id')}", default=str(c.get("id")) == str(self.selected_id))
                for c in chunk], row=0))
        cannon = self.current()
        part = self.active_part()
        if cannon and cannon.get("parts"):
            parts = cannon["parts"]
            if not part:
                self.active_part_id = str(parts[0]["id"])
                part = parts[0]
            self.add_item(_DetailChoiceSelect(self, "設定する部位を選択", [
                discord.SelectOption(label=str(p.get("name", "部位"))[:100], value=str(p["id"]),
                                     default=str(p["id"]) == str(self.active_part_id)) for p in parts], row=1))
            min_lv, max_lv = int(part.get("min_level", 0)), int(part.get("max_level", 0))
            pages = max(1, (max_lv - min_lv + 25) // 25)
            self.level_page = max(0, min(self.level_page, pages - 1))
            ranges = []
            for page in range(pages):
                lo = min_lv + page * 25
                hi = min(max_lv, lo + 24)
                ranges.append(discord.SelectOption(label=f"Lv.{lo}〜{hi}", value=str(page), default=page == self.level_page))
            self.add_item(_DetailChoiceSelect(self, "レベル帯を選択", ranges, row=2))
            lo = min_lv + self.level_page * 25
            hi = min(max_lv, lo + 24)
            current = self._current_level(cannon, part)
            level_options = [discord.SelectOption(label=f"Lv.{lv}", value=str(lv), default=lv == current) for lv in range(lo, hi + 1)]
            self.add_item(_DetailChoiceSelect(self, "部位のレベルを選択", level_options, row=3))
        if self.max_page:
            self.add_item(_DetailPagerButton(self, -1, row=4))
            self.add_item(_DetailPagerButton(self, 1, row=4))
        add_button = ui.Button(label="➕ この城を追加/更新", style=discord.ButtonStyle.primary, row=4)
        finish_button = ui.Button(label="✅ 設定を確定", style=discord.ButtonStyle.success, row=4)
        async def add_callback(interaction):
            cannon = self.current()
            if not cannon:
                await interaction.response.send_message("❌ 城強化を選択してください。", ephemeral=True); return
            levels = {str(p["id"]): self._current_level(cannon, p) for p in cannon.get("parts", [])}
            self.settings[str(cannon["id"])] = {"levels": levels}
            self.refresh()
            await interaction.response.edit_message(embed=self.make_embed(), view=self)
        async def finish_callback(interaction):
            if not self.settings:
                await interaction.response.send_message("❌ 城を1つ以上「この城を追加/更新」してください。", ephemeral=True); return
            key = f"ototo_detail|{json.dumps(self.settings, ensure_ascii=False, separators=(',', ':'))}"
            await _detail_key_to_parent(interaction, key, "オトート・城強化詳細指定", self.parent_view)
        add_button.callback = add_callback
        finish_button.callback = finish_callback
        self.add_item(add_button)
        self.add_item(finish_button)

    def on_choice(self, select, values):
        value = values[0]
        if select.placeholder == "城強化を選択":
            self.selected_id = value
            cannon = self.current()
            self.active_part_id = str(cannon["parts"][0]["id"]) if cannon and cannon.get("parts") else None
            self.level_page = 0
        elif select.placeholder == "設定する部位を選択":
            self.active_part_id = value
            self.level_page = 0
        elif select.placeholder == "レベル帯を選択":
            self.level_page = int(value)
        elif select.placeholder == "部位のレベルを選択":
            cannon = self.current()
            if cannon and self.active_part_id is not None:
                self.selected_parts.setdefault(str(cannon["id"]), {})[str(self.active_part_id)] = int(value)


class LineupSlotFormModal(ui.Modal):
    def __init__(self, parent, slot_index):
        super().__init__(title=f"編成{parent.lineup}｜枠{slot_index+1}")
        self.parent_view = parent
        self.slot_index = slot_index
        self.cat_id = ui.TextInput(
            label="キャラID",
            placeholder="数字で入力（例: 123）",
            required=True,
            max_length=5,
        )
        self.form = ui.TextInput(
            label="形態（1〜4）",
            placeholder="例: 1",
            required=True,
            max_length=1,
        )
        self.add_item(self.cat_id)
        self.add_item(self.form)

    async def on_submit(self, interaction):
        try:
            cid = int(self.cat_id.value.strip())
            form = int(self.form.value.strip())
            if cid < 1 or not 1 <= form <= 4:
                raise ValueError
        except ValueError:
            await interaction.response.send_message("❌ キャラIDは1以上、形態は1〜4で入力してください。", ephemeral=True)
            return
        self.parent_view.cats[self.slot_index] = cid
        self.parent_view.forms[self.slot_index] = form
        self.parent_view.refresh()
        await interaction.response.edit_message(
            content=f"✅ 編成{self.parent_view.lineup}・枠{self.slot_index+1} → キャラID {cid} / {form}形態",
            view=self.parent_view,
        )


class LineupSlotSelect(ui.Select):
    def __init__(self, owner):
        self.owner = owner
        options = [
            discord.SelectOption(
                label=f"枠{i+1}",
                value=str(i),
                description=(
                    f"ID {owner.cats[i]} / {owner.forms[i]}形態"
                    if owner.cats[i] is not None else "未設定"
                ),
            )
            for i in range(10)
        ]
        super().__init__(
            placeholder="設定する枠を選択（1〜10）",
            min_values=1, max_values=1, row=1,
            options=options,
        )

    async def callback(self, interaction):
        await interaction.response.send_modal(
            LineupSlotFormModal(self.owner, int(self.values[0]))
        )


class LineupNumberSelect(ui.Select):
    def __init__(self, owner):
        self.owner = owner
        super().__init__(
            placeholder=f"編成番号（現在 {owner.lineup}）",
            min_values=1, max_values=1, row=0,
            options=[
                discord.SelectOption(label=f"編成{i}", value=str(i), default=i == owner.lineup)
                for i in range(1, 21)
            ],
        )

    async def callback(self, interaction):
        self.owner.lineup = int(self.values[0])
        self.owner.refresh()
        await interaction.response.edit_message(view=self.owner)


class LineupFinishButton(ui.Button):
    def __init__(self, owner):
        self.owner = owner
        super().__init__(label="✅ この編成を追加", style=discord.ButtonStyle.success, row=2)

    async def callback(self, interaction):
        settings = {
            "lineup": self.owner.lineup,
            "cats": self.owner.cats,
            "forms": self.owner.forms,
        }
        key = f"lineup_detail|{json.dumps(settings, ensure_ascii=False, separators=(',', ':'))}"
        await _detail_key_to_parent(
            interaction,
            key,
            f"編成{self.owner.lineup}を個別設定",
            self.owner.parent_view,
        )


class LineupDetailView(ui.View):
    def __init__(self, parent_view=None):
        super().__init__(timeout=300)
        self.parent_view = parent_view
        self.lineup = 1
        self.cats = [None] * 10
        self.forms = [1] * 10
        self.refresh()

    def refresh(self):
        self.clear_items()
        self.add_item(LineupNumberSelect(self))
        self.add_item(LineupSlotSelect(self))
        self.add_item(LineupFinishButton(self))

    def summary(self):
        return "\n".join(
            f"枠{i+1}: {'未設定' if self.cats[i] is None else f'ID {self.cats[i]} / {self.forms[i]}形態'}"
            for i in range(10)
        )


class LineupDetailModal:
    """互換名。実際には10枠を個別に設定できるSelect+Modal UI。"""
    def __init__(self, parent_view=None):
        self.parent_view = parent_view

    async def open(self, interaction):
        view = LineupDetailView(self.parent_view)
        await interaction.response.send_message(
            embed=discord.Embed(
                title="🧩 編成キャラ個別設定",
                description="編成番号を1〜20から選択し、枠1〜10を選ぶと、その枠のキャラIDと形態を入力できます。",
                color=0x38bdf8,
            ),
            view=view,
            ephemeral=True,
        )


class _DetailChoiceSelect(ui.Select):
    def __init__(self, owner, placeholder, options, *, min_values=1, max_values=1, row=0):
        self.owner = owner
        super().__init__(placeholder=placeholder, options=options[:25], min_values=min_values,
                         max_values=min(max_values, len(options[:25])), row=row)
    async def callback(self, interaction):
        self.owner.on_choice(self, self.values)
        self.owner.refresh()
        await interaction.response.edit_message(embed=self.owner.make_embed(), view=self.owner)

class _DetailPagerButton(ui.Button):
    def __init__(self, owner, delta, row=4):
        self.owner=owner; self.delta=delta
        super().__init__(label='◀ 前へ' if delta < 0 else '次へ ▶', style=discord.ButtonStyle.secondary, row=row)
    async def callback(self, interaction):
        self.owner.page=max(0, min(self.owner.max_page, self.owner.page+self.delta))
        self.owner.refresh()
        await interaction.response.edit_message(embed=self.owner.make_embed(), view=self.owner)

class _DetailFinishButton(ui.Button):
    def __init__(self, owner, label='✅ この内容を追加'):
        self.owner=owner
        super().__init__(label=label, style=discord.ButtonStyle.success, row=4)
    async def callback(self, interaction):
        await self.owner.finish(interaction)

class FacilityDetailModal:
    """vip.htmlの施設名/最大レベル情報を使ったセレクト式設定。"""
    def __init__(self, parent_view=None):
        self.parent_view=parent_view
    async def open(self, interaction):
        view=FacilityDetailView(self.parent_view)
        await interaction.response.send_message(embed=view.make_embed(), view=view, ephemeral=True)

class FacilityDetailView(ui.View):
    """施設ID 0〜9、基礎Lv、+値を全レベル選択でき、複数施設を追加できる。"""
    def __init__(self, parent_view=None):
        super().__init__(timeout=300)
        self.parent_view = parent_view
        self.facilities = [x for x in get_legend_metadata().get("facilities", []) if 0 <= int(x.get("id", -1)) <= 9]
        self.facility_id = str(self.facilities[0]["id"]) if self.facilities else None
        self.base_level = 0
        self.plus_level = 0
        self.base_page = 0
        self.plus_page = 0
        self.settings = {}
        self.refresh()

    @property
    def current(self):
        return next((x for x in self.facilities if str(x.get("id")) == self.facility_id), None)

    def _base_max(self):
        return max(0, int(self.current.get("max_base", 0))) if self.current else 0

    def _plus_max(self):
        return max(0, int(self.current.get("max_plus", 0))) if self.current else 0

    def make_embed(self):
        current = self.current
        selected = (f"ID {current['id']}：{current['name']} / 基礎Lv.{self.base_level} / ＋{self.plus_level}" if current else "施設なし")
        summary = "\n".join(
            f"ID {fid} {next((x['name'] for x in self.facilities if str(x.get('id')) == str(fid)), '施設'+str(fid))}：基礎Lv.{v['base']} / ＋{v['plus']}"
            for fid, v in self.settings.items()) or "まだ設定されていません"
        return discord.Embed(title="🏭 施設ごとのレベル指定", description=(
            "施設ID 0〜9から選び、基礎Lv・＋値を選択して追加してください。全レベルをページ切替で選べます。複数施設対応。\n\n"
            f"**選択中**\n{selected}\n\n**設定済み**\n{summary}"), color=0x38bdf8)

    def refresh(self):
        self.clear_items()
        if not self.facilities:
            return
        self.add_item(_DetailChoiceSelect(self, "施設を選択（ID 0〜9）", [
            discord.SelectOption(label=f"ID {x['id']}：{str(x['name'])[:90]}", value=str(x['id']),
                                 description=f"基礎最大Lv {x.get('max_base', 0)} / ＋最大 {x.get('max_plus', 0)}",
                                 default=str(x['id']) == str(self.facility_id)) for x in self.facilities], row=0))
        base_max, plus_max = self._base_max(), self._plus_max()
        self.base_page = max(0, min(self.base_page, base_max // 25))
        self.plus_page = max(0, min(self.plus_page, plus_max // 25))
        base_lo, base_hi = self.base_page * 25, min(base_max, self.base_page * 25 + 24)
        plus_lo, plus_hi = self.plus_page * 25, min(plus_max, self.plus_page * 25 + 24)
        self.add_item(_DetailChoiceSelect(self, "基礎Lvを選択", [
            discord.SelectOption(label=f"基礎Lv {lv}", value=str(lv), default=lv == self.base_level)
            for lv in range(base_lo, base_hi + 1)], row=1))
        self.add_item(_DetailChoiceSelect(self, "＋値を選択", [
            discord.SelectOption(label=f"＋{lv}", value=str(lv), default=lv == self.plus_level)
            for lv in range(plus_lo, plus_hi + 1)], row=2))
        if base_max >= 25:
            bprev = ui.Button(label="基礎Lv ◀", style=discord.ButtonStyle.secondary, row=3, disabled=self.base_page <= 0)
            bnext = ui.Button(label="基礎Lv ▶", style=discord.ButtonStyle.secondary, row=3, disabled=base_lo + 25 > base_max)
            async def bp_cb(i): self.base_page -= 1; self.refresh(); await i.response.edit_message(embed=self.make_embed(), view=self)
            async def bn_cb(i): self.base_page += 1; self.refresh(); await i.response.edit_message(embed=self.make_embed(), view=self)
            bprev.callback, bnext.callback = bp_cb, bn_cb
            self.add_item(bprev); self.add_item(bnext)
        if plus_max >= 25:
            pprev = ui.Button(label="＋値 ◀", style=discord.ButtonStyle.secondary, row=3, disabled=self.plus_page <= 0)
            pnext = ui.Button(label="＋値 ▶", style=discord.ButtonStyle.secondary, row=3, disabled=plus_lo + 25 > plus_max)
            async def pp_cb(i): self.plus_page -= 1; self.refresh(); await i.response.edit_message(embed=self.make_embed(), view=self)
            async def pn_cb(i): self.plus_page += 1; self.refresh(); await i.response.edit_message(embed=self.make_embed(), view=self)
            pprev.callback, pnext.callback = pp_cb, pn_cb
            self.add_item(pprev); self.add_item(pnext)
        add_button = ui.Button(label="➕ 設定を追加/更新", style=discord.ButtonStyle.primary, row=4)
        finish_button = ui.Button(label="✅ この内容を追加", style=discord.ButtonStyle.success, row=4)
        async def add_callback(interaction):
            if self.facility_id is None:
                await interaction.response.send_message("❌ 施設を選択してください。", ephemeral=True); return
            self.settings[self.facility_id] = {"base": int(self.base_level), "plus": int(self.plus_level)}
            self.refresh(); await interaction.response.edit_message(embed=self.make_embed(), view=self)
        async def finish_callback(interaction):
            if not self.settings:
                await interaction.response.send_message("❌ 施設を1つ以上追加してください。", ephemeral=True); return
            key = f"facility_detail|{json.dumps(self.settings, ensure_ascii=False, separators=(',', ':'))}"
            await _detail_key_to_parent(interaction, key, "施設ごとのレベル指定", self.parent_view)
        add_button.callback, finish_button.callback = add_callback, finish_callback
        self.add_item(add_button); self.add_item(finish_button)

    def on_choice(self, select, values):
        value = values[0]
        if select.placeholder.startswith("施設を選択"):
            self.facility_id = value
            self.base_level = min(self.base_level, self._base_max())
            self.plus_level = min(self.plus_level, self._plus_max())
            self.base_page = self.base_level // 25
            self.plus_page = self.plus_level // 25
        elif select.placeholder == "基礎Lvを選択":
            self.base_level = int(value)
        elif select.placeholder == "＋値を選択":
            self.plus_level = int(value)


class TalentOrbDetailModal:
    """本能玉の種類・ランクを名前から選び、個数を候補から設定する。"""
    def __init__(self,parent_view=None): self.parent_view=parent_view
    async def open(self,interaction):
        view=TalentOrbDetailView(self.parent_view)
        await interaction.response.send_message(embed=view.make_embed(),view=view,ephemeral=True)

class TalentOrbDetailView(ui.View):
    def __init__(self,parent_view=None):
        super().__init__(timeout=300); self.parent_view=parent_view
        self.orbs=[(g,r) for g in get_legend_metadata().get('talent_orbs',[]) for r in g.get('ranks',[])]
        self.page=0; self.selected_id=str(self.orbs[0][1]['id']) if self.orbs else None
        self.amount='998'; self.settings={}; self.refresh()
    @property
    def max_page(self): return max(0,(len(self.orbs)-1)//25)
    def make_embed(self):
        current=next(((g,r) for g,r in self.orbs if str(r['id'])==self.selected_id),None)
        summary='\n'.join(f"{next((g['name']+' '+str(r.get('rank','')) for g,r in self.orbs if str(r['id'])==k), '本能玉 '+k)}：{v}個" for k,v in self.settings.items()) or 'まだ設定されていません'
        return discord.Embed(title='💎 本能玉名 → ランク 個別選択',description=f"種類・ランクを選び、設定する個数を選んで「設定を追加」。\nページ {self.page+1}/{self.max_page+1}\n選択中：{current[0]['name']} / {current[1].get('rank','ランク不明')}\n\n**設定済み**\n{summary}",color=0x38bdf8)
    def refresh(self):
        self.clear_items(); start=self.page*25; chunk=self.orbs[start:start+25]
        if chunk:
            self.add_item(_DetailChoiceSelect(self,'本能玉名・ランクを選択',[discord.SelectOption(label=f"{g['name']}｜{r.get('rank','ランク不明')}"[:100],value=str(r['id']),description=f"ID {r['id']}") for g,r in chunk],row=0))
        self.add_item(_DetailChoiceSelect(self,'設定する個数を選択',[discord.SelectOption(label=f'{x}個',value=str(x),default=str(x)==self.amount) for x in [0,1,10,50,99,500,998]],row=1))
        self.add_item(ui.Button(label='設定を追加',style=discord.ButtonStyle.primary,row=2,custom_id='orb_add')); self.children[-1].callback=self.add_setting
        if self.max_page: self.add_item(_DetailPagerButton(self,-1,row=3)); self.add_item(_DetailPagerButton(self,1,row=3))
        self.add_item(_DetailFinishButton(self))
    def on_choice(self,select,values):
        if select.placeholder=='本能玉名・ランクを選択': self.selected_id=values[0]
        elif select.placeholder=='設定する個数を選択': self.amount=values[0]
    async def add_setting(self,interaction):
        if self.selected_id is not None: self.settings[self.selected_id]=int(self.amount)
        self.refresh(); await interaction.response.edit_message(embed=self.make_embed(),view=self)
    async def finish(self,interaction):
        if not self.settings: await interaction.response.send_message('本能玉と個数を選択して「設定を追加」してください。',ephemeral=True); return
        key=f"talent_orb_detail|{json.dumps({int(k):v for k,v in self.settings.items()},separators=(',',':'))}"
        await _detail_key_to_parent(interaction,key,'本能玉名 → ランク 個別選択',self.parent_view)

class EventTicketDetailModal:
    """vip.htmlから取得したイベントチケット名を選ぶUI。"""
    def __init__(self,parent_view=None): self.parent_view=parent_view
    async def open(self,interaction):
        view=EventTicketDetailView(self.parent_view)
        await interaction.response.send_message(embed=view.make_embed(),view=view,ephemeral=True)

class EventTicketDetailView(ui.View):
    def __init__(self,parent_view=None):
        super().__init__(timeout=300); self.parent_view=parent_view
        self.tickets=get_legend_metadata().get('event_tickets',[]); self.page=0
        self.ticket_id=str(self.tickets[0]['id']) if self.tickets else None
        self.amount='9999'; self.settings={}; self.refresh()
    @property
    def max_page(self): return max(0,(len(self.tickets)-1)//25)
    def make_embed(self):
        current=next((t for t in self.tickets if str(t['id'])==self.ticket_id),None)
        summary='\n'.join(f"{next((t['label'] for t in self.tickets if str(t['id'])==k),k)}：{v}個" for k,v in self.settings.items()) or 'まだ設定されていません'
        return discord.Embed(title='🎟️ イベントチケット 種類別選択',description=f"チケット名を選んで個数を指定してください。\nページ {self.page+1}/{self.max_page+1}\n選択中：{current['label'] if current else 'なし'}\n\n**設定済み**\n{summary}",color=0x38bdf8)
    def refresh(self):
        self.clear_items(); chunk=self.tickets[self.page*25:(self.page+1)*25]
        if chunk: self.add_item(_DetailChoiceSelect(self,'チケット名・保存枠を選択',[discord.SelectOption(label=str(t['label'])[:100],value=str(t['id'])) for t in chunk],row=0))
        self.add_item(_DetailChoiceSelect(self,'設定する個数を選択',[discord.SelectOption(label=f'{x}個',value=str(x),default=str(x)==self.amount) for x in [0,1,10,50,99,500,999,9999]],row=1))
        self.add_item(ui.Button(label='設定を追加',style=discord.ButtonStyle.primary,row=2,custom_id='ticket_add')); self.children[-1].callback=self.add_setting
        if self.max_page: self.add_item(_DetailPagerButton(self,-1,row=3)); self.add_item(_DetailPagerButton(self,1,row=3))
        self.add_item(_DetailFinishButton(self))
    def on_choice(self,select,values):
        if select.placeholder=='チケット名・保存枠を選択': self.ticket_id=values[0]
        elif select.placeholder=='設定する個数を選択': self.amount=values[0]
    async def add_setting(self,interaction):
        if self.ticket_id is not None: self.settings[self.ticket_id]=int(self.amount)
        self.refresh(); await interaction.response.edit_message(embed=self.make_embed(),view=self)
    async def finish(self,interaction):
        if not self.settings: await interaction.response.send_message('チケットと個数を選択して「設定を追加」してください。',ephemeral=True); return
        key=f"event_ticket_detail|{json.dumps(self.settings,separators=(',',':'))}"
        await _detail_key_to_parent(interaction,key,'イベントチケット 種類別選択',self.parent_view)

class LabyrinthDetailModal:
    """地底迷宮の操作と対象キャラをセレクトで指定。"""
    def __init__(self,parent_view=None): self.parent_view=parent_view
    async def open(self,interaction):
        view=LabyrinthDetailView(self.parent_view)
        await interaction.response.send_message(embed=view.make_embed(),view=view,ephemeral=True)

class LabyrinthDetailView(ui.View):
    ACTIONS=[('選択キャラを封印','seal_selected'),('選択キャラを解放','unlock_selected'),('全キャラを封印','seal_all'),('全キャラを解放','unlock_all'),('編成キャラを全解放','release_lineup_all')]
    def __init__(self,parent_view=None):
        super().__init__(timeout=300); self.parent_view=parent_view; self.action='seal_selected'; self.ids=[]; self.page=0
        try: self.characters=get_character_metadata().get('characters',[])
        except Exception: self.characters=[]
        self.refresh()
    @property
    def max_page(self): return max(0,(len(self.characters)-1)//25)
    def make_embed(self):
        names={int(c['id']):(c.get('names') or [f"キャラID {c['id']}"])[0] for c in self.characters if str(c.get('id','')).isdigit()}
        selected=', '.join(names.get(i,str(i)) for i in self.ids) or 'なし'
        act=dict((v,k) for k,v in self.ACTIONS).get(self.action,self.action)
        return discord.Embed(title='🌀 地底迷宮詳細指定',description=f"操作を選択してください。対象キャラを選択操作にした場合は、キャラ一覧から選択できます。\n操作：**{act}**\n対象：{selected}\nキャラ一覧ページ {self.page+1}/{self.max_page+1}",color=0x38bdf8)
    def refresh(self):
        self.clear_items(); self.add_item(_DetailChoiceSelect(self,'地底迷宮の操作を選択',[discord.SelectOption(label=k,value=v,default=v==self.action) for k,v in self.ACTIONS],row=0))
        chunk=self.characters[self.page*25:(self.page+1)*25]
        opts=[]
        for c in chunk:
            try: cid=int(c.get('id'))
            except (TypeError,ValueError): continue
            name=str(c.get('name') or ((c.get('names') or [f'キャラID {cid}'])[0]))
            opts.append(discord.SelectOption(label=f'{name}'[:100],value=str(cid),description=f'ID {cid}',default=cid in self.ids))
        if opts: self.add_item(_DetailChoiceSelect(self,'対象キャラを複数選択（最大25）',opts,min_values=0,max_values=len(opts),row=1))
        if self.max_page: self.add_item(_DetailPagerButton(self,-1,row=2)); self.add_item(_DetailPagerButton(self,1,row=2))
        self.add_item(_DetailFinishButton(self))
    def on_choice(self,select,values):
        if select.placeholder=='地底迷宮の操作を選択': self.action=values[0]
        else:
            chunk=self.characters[self.page*25:(self.page+1)*25]
            page_ids={int(c['id']) for c in chunk if str(c.get('id','')).isdigit()}
            self.ids=[x for x in self.ids if x not in page_ids]+[int(x) for x in values]
            self.ids=list(dict.fromkeys(self.ids))
    async def finish(self,interaction):
        if self.action in {'seal_selected','unlock_selected'} and not self.ids:
            await interaction.response.send_message('選択操作には対象キャラを1体以上選んでください。',ephemeral=True); return
        key=f"labyrinth_detail|{json.dumps({'action':self.action,'ids':self.ids},separators=(',',':'))}"
        await _detail_key_to_parent(interaction,key,'地底迷宮詳細指定',self.parent_view)

class MainStageCountModal(ui.Modal):
    def __init__(self, parent, stage_ids):
        super().__init__(title="メイン章・ステージ回数")
        self.parent = parent
        self.stage_ids = stage_ids
        self.count = ui.TextInput(label="回数", placeholder="例: 1", default="1", required=True, max_length=5)
        self.add_item(self.count)

    async def on_submit(self, interaction):
        try:
            count = max(1, int(self.count.value.strip()))
        except ValueError:
            await interaction.response.send_message("❌ 回数は数字で入力してください。", ephemeral=True)
            return
        result = {}
        for position in self.parent.positions:
            result[str(position)] = {str(s): count for s in self.stage_ids}
        key = f"main_stage_detail|{json.dumps(result, ensure_ascii=False, separators=(',', ':'))}"
        await _detail_key_to_parent(interaction, key, "メイン章・ステージ個別指定", self.parent.parent_view)


class MainStorySeriesSelect(ui.Select):
    def __init__(self, owner):
        self.owner = owner
        super().__init__(
            placeholder="種別を選択（日本編 / 未来編 / 宇宙編）",
            min_values=1, max_values=1, row=0,
            options=[
                discord.SelectOption(label="日本編", value="japan"),
                discord.SelectOption(label="未来編", value="future"),
                discord.SelectOption(label="宇宙編", value="space"),
            ],
        )

    async def callback(self, interaction):
        self.owner.series = self.values[0]
        base = {"japan": 0, "future": 3, "space": 6}[self.owner.series]
        self.owner.positions = [base + i for i in range(3)]
        self.owner.stage_names = self.owner.series_stage_names.get(self.owner.series, [])
        self.owner.stage_ids = []
        self.owner.stage_page = 0
        self.owner.refresh()
        await interaction.response.edit_message(view=self.owner)


class MainStoryChapterSelect(ui.Select):
    def __init__(self, owner):
        self.owner = owner
        base = {"japan": 0, "future": 3, "space": 6}[owner.series]
        super().__init__(
            placeholder="章を選択（1〜3章・複数可）",
            min_values=1, max_values=3, row=1,
            options=[
                discord.SelectOption(label=f"{i+1}章", value=str(base+i), default=(base+i in owner.positions))
                for i in range(3)
            ],
        )

    async def callback(self, interaction):
        self.owner.positions = [int(v) for v in self.values]
        # 章を変えてもステージ一覧は変えない。
        await interaction.response.edit_message(view=self.owner)


class MainStoryStageSelect(ui.Select):
    def __init__(self, owner):
        self.owner = owner
        start = owner.stage_page * 25
        page_rows = list(enumerate(owner.stage_names))[start:start + 25]
        options = [
            discord.SelectOption(label=f"{i+1}. {str(name)[:90]}", value=str(i),
                                 default=i in owner.stage_ids)
            for i, name in page_rows
        ] or [discord.SelectOption(label="ステージなし", value="none")]
        super().__init__(
            placeholder=f"ステージ一覧（複数選択可）｜ページ {owner.stage_page + 1}",
            min_values=1, max_values=min(len(options), 25), row=2,
            options=options,
        )

    async def callback(self, interaction):
        chosen = [int(v) for v in self.values if v != "none"]
        self.owner.stage_ids = list(dict.fromkeys(self.owner.stage_ids + chosen))
        self.owner.refresh()
        await interaction.response.edit_message(view=self.owner)


class MainStoryFinishButton(ui.Button):
    def __init__(self, owner):
        self.owner = owner
        super().__init__(label="➡️ 回数を指定", style=discord.ButtonStyle.success, row=3)

    async def callback(self, interaction):
        if not self.owner.stage_ids or not self.owner.positions:
            await interaction.response.send_message("❌ 章とステージを選択してください。", ephemeral=True)
            return
        await interaction.response.send_modal(
            MainStageCountModal(self.owner, self.owner.stage_ids)
        )


class MainStageDetailView(ui.View):
    def __init__(self, parent_view=None):
        super().__init__(timeout=300)
        self.parent_view = parent_view
        self.series = "japan"
        self.positions = [0]
        self.stage_names = []
        self.series_stage_names = {}
        self.stage_ids = []
        self.stage_page = 0
        self.refresh()

    async def initialize(self, interaction):
        try:
            metadata = await _stage_metadata()
            chapters = metadata.get("main_story", {}).get("chapters", [])
            # 日本/未来/宇宙ごとにステージ名を取得。各章で同一の48ステージ名を使う。
            self.series_stage_names = {
                "japan": list(chapters[0].get("stages", [])) if len(chapters) >= 3 else [],
                "future": list(chapters[3].get("stages", [])) if len(chapters) >= 6 else [],
                "space": list(chapters[6].get("stages", [])) if len(chapters) >= 9 else [],
            }
            self.stage_names = self.series_stage_names["japan"]
        except Exception:
            await interaction.response.send_message("❌ メインステージ一覧の取得に失敗しました。", ephemeral=True)
            return
        self.refresh()
        await interaction.response.send_message(
            embed=discord.Embed(
                title="🗺️ メイン章・ステージ個別指定",
                description="日本編・未来編・宇宙編を選択 → 1〜3章を選択 → ステージ一覧を選択 → 回数を入力。\n※章を変更してもステージ一覧は変わりません。",
                color=0x38bdf8,
            ),
            view=self,
            ephemeral=True,
        )

    def refresh(self):
        self.clear_items()
        self.add_item(MainStorySeriesSelect(self))
        self.add_item(MainStoryChapterSelect(self))
        self.add_item(MainStoryStageSelect(self))
        self.add_item(MainStoryFinishButton(self))
        if len(self.stage_names) > 25:
            self.add_item(_StagePagerButton(self, -1))
            self.add_item(_StagePagerButton(self, 1))


class MainStageDetailModal:
    def __init__(self, parent_view=None):
        self.parent_view = parent_view

    async def open(self, interaction):
        view = MainStageDetailView(self.parent_view)
        await view.initialize(interaction)



class SpecialStageTypeSelect(ui.Select):
    def __init__(self, owner):
        self.owner = owner
        super().__init__(
            placeholder="種別を選択",
            min_values=1, max_values=1, row=0,
            options=[
                discord.SelectOption(label="ゾンビ襲来", value="zombie"),
                discord.SelectOption(label="魔界編", value="aku"),
                discord.SelectOption(label="魔界編EX", value="aku_ex"),
            ],
        )

    async def callback(self, interaction):
        self.owner.kind = self.values[0]
        self.owner.chapter = 0
        self.owner.selected_stages = []
        self.owner.stage_page = 0
        self.owner.refresh()
        await interaction.response.edit_message(view=self.owner)


class SpecialStageChapterSelect(ui.Select):
    def __init__(self, owner):
        self.owner = owner
        chapters = owner.metadata.get("zombie", {}).get("chapters", []) if owner.kind == "zombie" else owner.metadata.get(owner.kind, {}).get("chapters", [])
        options = [
            discord.SelectOption(label=str(c.get("name", f"{int(c.get('id',0))+1}章"))[:100], value=str(c.get("id", 0)))
            for c in chapters[:25]
        ]
        super().__init__(
            placeholder="章を選択" if owner.kind == "zombie" else "章（固定）",
            min_values=1, max_values=1,
            row=1,
            options=options or [discord.SelectOption(label="章なし", value="0")],
        )

    async def callback(self, interaction):
        self.owner.chapter = int(self.values[0])
        self.owner.selected_stages = []
        self.owner.stage_page = 0
        self.owner.refresh()
        await interaction.response.edit_message(view=self.owner)


class SpecialStageSelect(ui.Select):
    def __init__(self, owner):
        chapters = owner.metadata.get("zombie", {}).get("chapters", []) if owner.kind == "zombie" else owner.metadata.get(owner.kind, {}).get("chapters", [])
        chapter = next((c for c in chapters if int(c.get("id", 0)) == owner.chapter), None)
        stages = chapter.get("stages", []) if chapter else []
        start = owner.stage_page * 25
        page_rows = list(enumerate(stages))[start:start + 25]
        options = [
            discord.SelectOption(label=f"{i+1}. {str(name)[:90]}", value=str(i),
                                 default=i in owner.selected_stages)
            for i, name in page_rows
        ] or [discord.SelectOption(label="ステージなし", value="none")]
        super().__init__(
            placeholder=f"ステージ一覧（複数選択可）｜ページ {owner.stage_page + 1}",
            min_values=1, max_values=min(len(options), 25), row=2,
            options=options,
        )

    async def callback(self, interaction):
        chosen = [int(v) for v in self.values if v != "none"]
        self.owner.selected_stages = list(dict.fromkeys(self.owner.selected_stages + chosen))
        self.owner.refresh()
        await interaction.response.edit_message(view=self.owner)


class SpecialStageFinishButton(ui.Button):
    def __init__(self, owner):
        self.owner = owner
        super().__init__(label="✅ この内容を追加", style=discord.ButtonStyle.success, row=3)

    async def callback(self, interaction):
        if not self.owner.selected_stages:
            await interaction.response.send_message("❌ ステージ一覧から選択してください。", ephemeral=True)
            return
        if self.owner.kind == "zombie":
            payload = {"zombie": {str(self.owner.chapter): self.owner.selected_stages}}
        elif self.owner.kind == "aku":
            payload = {"aku": self.owner.selected_stages}
        else:
            payload = {"aku_ex": self.owner.selected_stages}
        key = f"special_stage_detail|{json.dumps(payload, ensure_ascii=False, separators=(',', ':'))}"
        await _detail_key_to_parent(interaction, key, "ゾンビ・魔界編詳細指定", self.owner.parent_view)


class SpecialStageDetailView(ui.View):
    def __init__(self, parent_view=None):
        super().__init__(timeout=300)
        self.parent_view = parent_view
        self.kind = "zombie"
        self.chapter = 0
        self.selected_stages = []
        self.metadata = {}
        self.stage_page = 0
        self.refresh()

    async def initialize(self, interaction):
        try:
            self.metadata = await _stage_metadata()
        except Exception:
            await interaction.response.send_message("❌ ゾンビ・魔界編のステージ一覧取得に失敗しました。", ephemeral=True)
            return
        self.refresh()
        await interaction.response.send_message(
            embed=discord.Embed(
                title="🧟 ゾンビ・魔界編詳細指定",
                description="種別を選択 → 必要なら章を選択 → ステージ一覧から選択してください。",
                color=0x38bdf8,
            ),
            view=self,
            ephemeral=True,
        )

    def refresh(self):
        self.clear_items()
        self.add_item(SpecialStageTypeSelect(self))
        self.add_item(SpecialStageChapterSelect(self))
        self.add_item(SpecialStageSelect(self))
        self.add_item(SpecialStageFinishButton(self))
        stages = self.metadata.get("zombie", {}).get("chapters", []) if self.kind == "zombie" else self.metadata.get(self.kind, {}).get("chapters", [])
        chapter = next((c for c in stages if int(c.get("id", 0)) == self.chapter), None)
        if chapter and len(chapter.get("stages", [])) > 25:
            self.add_item(_StagePagerButton(self, -1))
            self.add_item(_StagePagerButton(self, 1))


class SpecialStageDetailModal:
    def __init__(self, parent_view=None):
        self.parent_view = parent_view

    async def open(self, interaction):
        view = SpecialStageDetailView(self.parent_view)
        await view.initialize(interaction)


class FacilityDetailModal:
    """施設ID(0〜9)・基礎Lv・+値をSelectで個別指定する。"""
    def __init__(self, parent_view=None):
        self.parent_view = parent_view

    async def open(self, interaction):
        view = FacilityDetailView(self.parent_view)
        await interaction.response.send_message(
            embed=view.make_embed(),
            view=view,
            ephemeral=True,
        )


class FacilityDetailView(ui.View):
    def __init__(self, parent_view=None):
        super().__init__(timeout=300)
        self.parent_view = parent_view
        self.facilities = [x for x in get_legend_metadata().get("facilities", []) if 0 <= int(x.get("id", -1)) <= 9]
        self.facility_id = str(self.facilities[0]["id"]) if self.facilities else None
        self.base_level = 1
        self.plus_level = 0
        self.settings = {}
        self.refresh()

    @property
    def current(self):
        return next((x for x in self.facilities if str(x.get("id")) == self.facility_id), None)

    def _base_max(self):
        current = self.current
        return max(0, int(current.get("max_base", 0))) if current else 0

    def _plus_max(self):
        current = self.current
        return max(0, int(current.get("max_plus", 0))) if current else 0

    def make_embed(self):
        current = self.current
        if current:
            selected_text = f"ID {current['id']}：{current['name']} / 基礎Lv.{self.base_level} / ＋{self.plus_level}"
        else:
            selected_text = "施設なし"
        if self.settings:
            lines = []
            for fid, value in self.settings.items():
                spec = next((x for x in self.facilities if str(x.get("id")) == str(fid)), None)
                name = spec.get("name", f"施設{fid}") if spec else f"施設{fid}"
                lines.append(f"`{fid}` {name}：基礎Lv.{value['base']} / ＋{value['plus']}")
            summary = "\n".join(lines)
        else:
            summary = "まだ設定されていません"
        return discord.Embed(
            title="🏭 施設ごとのレベル指定",
            description=(
                "施設ID 0〜9から選択し、基礎Lvと＋値を指定して「設定を追加」。\n"
                "複数施設を追加できます。\n\n"
                f"**選択中**\n{selected_text}\n\n"
                f"**設定済み**\n{summary}"
            ),
            color=0x38bdf8,
        )

    def refresh(self):
        self.clear_items()
        if not self.facilities:
            return

        self.add_item(_DetailChoiceSelect(
            self,
            "施設を選択（ID 0〜9）",
            [
                discord.SelectOption(
                    label=f"ID {x['id']}：{str(x['name'])[:90]}",
                    value=str(x['id']),
                    description=f"基礎最大Lv {x.get('max_base', 0)} / ＋最大 {x.get('max_plus', 0)}",
                    default=str(x['id']) == str(self.facility_id),
                )
                for x in self.facilities
            ],
            row=0,
        ))

        base_max = self._base_max()
        # Discord Selectは25項目まで。通常の施設基礎Lvはこの範囲に収まる。
        base_options = [
            discord.SelectOption(label=f"基礎Lv {lv}", value=str(lv))
            for lv in range(0, min(base_max, 24) + 1)
        ] or [discord.SelectOption(label="基礎Lv 0", value="0")]
        self.add_item(_DetailChoiceSelect(
            self,
            "基礎Lvを選択",
            base_options,
            row=1,
        ))

        plus_max = self._plus_max()
        plus_options = [
            discord.SelectOption(label=f"＋{lv}", value=str(lv))
            for lv in range(0, min(plus_max, 24) + 1)
        ] or [discord.SelectOption(label="＋0", value="0")]
        self.add_item(_DetailChoiceSelect(
            self,
            "＋値を選択",
            plus_options,
            row=2,
        ))

        add_button = ui.Button(label="➕ 設定を追加", style=discord.ButtonStyle.primary, row=3)
        finish_button = ui.Button(label="✅ この内容を追加", style=discord.ButtonStyle.success, row=3)

        async def add_callback(interaction: discord.Interaction):
            if self.facility_id is None:
                await interaction.response.send_message("❌ 施設を選択してください。", ephemeral=True)
                return
            self.settings[self.facility_id] = {
                "base": int(self.base_level),
                "plus": int(self.plus_level),
            }
            self.refresh()
            await interaction.response.edit_message(embed=self.make_embed(), view=self)

        async def finish_callback(interaction: discord.Interaction):
            # 「この内容を追加」だけでも、現在選択中の施設とレベルを取り込む。
            # 「設定を追加」を先に押す必要がないようにする。
            if self.facility_id is not None:
                self.settings[self.facility_id] = {
                    "base": int(self.base_level),
                    "plus": int(self.plus_level),
                }
            if not self.settings:
                await interaction.response.send_message("❌ 施設を選択してください。", ephemeral=True)
                return
            key = f"facility_detail|{json.dumps(self.settings, ensure_ascii=False, separators=(',', ':'))}"
            await _detail_key_to_parent(interaction, key, "施設ごとのレベル指定", self.parent_view)

        add_button.callback = add_callback
        finish_button.callback = finish_callback
        self.add_item(add_button)
        self.add_item(finish_button)

    def on_choice(self, select, values):
        value = values[0]
        if select.placeholder.startswith("施設を選択"):
            self.facility_id = value
            current = self.current
            self.base_level = min(self.base_level, int(current.get("max_base", 0))) if current else 0
            self.plus_level = min(self.plus_level, int(current.get("max_plus", 0))) if current else 0
        elif select.placeholder == "基礎Lvを選択":
            self.base_level = int(value)
        elif select.placeholder == "＋値を選択":
            self.plus_level = int(value)

class TalentOrbDetailModal:
    """vip.html同様、本能玉名とランクを選択して個数を指定する。"""
    def __init__(self, parent_view=None):
        self.parent_view = parent_view

    async def open(self, interaction):
        view = TalentOrbDetailView(self.parent_view)
        await interaction.response.send_message(embed=view.make_embed(), view=view, ephemeral=True)


class EventTicketDetailModal:
    """vip.html同様、イベントチケット名・保存枠を選んで個数を指定する。"""
    def __init__(self, parent_view=None):
        self.parent_view = parent_view

    async def open(self, interaction):
        view = EventTicketDetailView(self.parent_view)
        await interaction.response.send_message(embed=view.make_embed(), view=view, ephemeral=True)


class EventStageCountModal(ui.Modal):
    def __init__(self, parent):
        super().__init__(title="イベントステージ｜クリア回数")
        self.parent = parent
        self.count = ui.TextInput(label="クリア回数", placeholder="例: 1", default="1", required=True, max_length=5)
        self.add_item(self.count)

    async def on_submit(self, interaction):
        try:
            count = max(1, int(self.count.value.strip()))
        except ValueError:
            await interaction.response.send_message("❌ 回数は数字で入力してください。", ephemeral=True)
            return
        fam = self.parent.family
        payload = {fam: {}}
        # イベント詳細指定では冠を使わず、常に1段階目(0)を処理する。
        star_key = "0"
        for mid in self.parent.selected_maps:
            # ステージ未選択なら、そのマップの全ステージを対象にする。
            map_obj = next((m for m in self.parent.maps if int(m.get("id", -1)) == int(mid)), None)
            if map_obj is None:
                continue
            stage_ids = list(self.parent.selected_stages)
            if not stage_ids:
                stage_ids = list(range(len(map_obj.get("stages", []))))
            payload[fam][str(mid)] = {
                star_key: {
                    str(sid): count for sid in stage_ids
                }
            }
        key = f"event_detail|{json.dumps(payload, ensure_ascii=False, separators=(',', ':'))}"
        await _detail_key_to_parent(interaction, key, f"イベント詳細 {self.parent.family_label}", self.parent.parent_view)


class EventFamilySelect(ui.Select):
    def __init__(self, owner):
        self.owner = owner
        options = [
            discord.SelectOption(label=str(spec["label"])[:100], value=key)
            for key, spec in EVENT_STAGE_FAMILIES.items()
        ]
        super().__init__(
            placeholder="種別を選択",
            min_values=1, max_values=1, row=0, options=options[:25],
        )

    async def callback(self, interaction):
        self.owner.family = self.values[0]
        self.owner.family_label = EVENT_STAGE_FAMILIES[self.owner.family]["label"]
        self.owner.crown = 1
        self.owner.selected_maps = []
        self.owner.selected_stages = []
        self.owner.page = 0
        self.owner.stage_page = 0
        self.owner.maps = list(self.owner.metadata.get("event_stage_families", {}).get(self.owner.family, {}).get("maps", []))
        self.owner.refresh()
        await interaction.response.edit_message(view=self.owner)


class EventMapSelect(ui.Select):
    def __init__(self, owner):
        self.owner = owner
        start = owner.page * 25
        rows = owner.maps[start:start+25]
        options = [
            discord.SelectOption(label=f"{int(m['id'])+1}. {str(m.get('name',''))[:90]}",
                                 value=str(m["id"]),
                                 default=int(m["id"]) in owner.selected_maps)
            for m in rows
        ] or [discord.SelectOption(label="マップなし", value="none")]
        super().__init__(
            placeholder=f"マップ一覧（複数選択可）｜ページ {owner.page + 1}",
            min_values=1, max_values=min(len(options),25), row=1, options=options,
            disabled=not bool(owner.family),
        )

    async def callback(self, interaction):
        self.owner.selected_maps = list(dict.fromkeys(
            self.owner.selected_maps + [int(v) for v in self.values if v != "none"]
        ))
        valid = {int(m["id"]) for m in self.owner.maps}
        self.owner.selected_maps = [x for x in self.owner.selected_maps if x in valid]
        self.owner.selected_stages = []
        self.owner.stage_page = 0
        self.owner.refresh()
        await interaction.response.edit_message(view=self.owner)


class EventCrownSelect(ui.Select):
    def __init__(self, owner):
        self.owner = owner
        super().__init__(
            placeholder=f"冠を選択（現在 {owner.crown}）",
            min_values=1, max_values=1, row=2,
            options=[discord.SelectOption(label=f"{i}冠", value=str(i), default=i == owner.crown) for i in range(1,5)],
        )

    async def callback(self, interaction):
        self.owner.crown = int(self.values[0])
        await interaction.response.edit_message(view=self.owner)


class EventStageSelect(ui.Select):
    def __init__(self, owner):
        rows = []
        for m in owner.maps:
            if int(m["id"]) not in owner.selected_maps:
                continue
            for sid, name in enumerate(m.get("stages", [])):
                rows.append((f"{str(m.get('name',''))[:28]}｜{sid+1}. {str(name)[:60]}", int(m["id"]), sid))
        start = owner.stage_page * 25
        page_rows = rows[start:start+25]
        options = [
            discord.SelectOption(label=label[:100], value=f"{mid}:{sid}", default=sid in owner.selected_stages)
            for label, mid, sid in page_rows
        ] or [discord.SelectOption(label="先にマップを選択してください", value="none")]
        super().__init__(
            placeholder=f"ステージ一覧（複数選択可）｜ページ {owner.stage_page + 1}",
            min_values=1, max_values=min(len(options),25), row=3, options=options,
            disabled=not bool(owner.family) or not bool(owner.selected_maps),
        )

    async def callback(self, interaction):
        selected_stage_ids = []
        for value in self.values:
            if value == "none":
                continue
            try:
                _mid, sid = value.split(":", 1)
                selected_stage_ids.append(int(sid))
            except (ValueError, TypeError):
                continue
        self.owner.selected_stages = list(dict.fromkeys(
            self.owner.selected_stages + selected_stage_ids
        ))
        self.owner.refresh()
        await interaction.response.edit_message(view=self.owner)


class EventFinishButton(ui.Button):
    def __init__(self, owner):
        self.owner = owner
        finish_row = 4
        super().__init__(label="➡️ 回数を指定", style=discord.ButtonStyle.success, row=finish_row)

    async def callback(self, interaction):
        if not self.owner.family:
            await interaction.response.send_message("❌ まず「種別を選択」から種別を選択してください。", ephemeral=True)
            return
        if not self.owner.selected_maps:
            await interaction.response.send_message("❌ マップ一覧からマップを選択してください。", ephemeral=True)
            return
        # ステージ一覧は未選択でもOK。選択したマップの全ステージに適用する。
        await interaction.response.send_modal(EventStageCountModal(self.owner))


class EventDetailView(ui.View):
    def __init__(self, parent_view=None):
        super().__init__(timeout=300)
        self.parent_view = parent_view
        self.metadata = {}
        # 種別は必須。初期状態では未選択にする。
        self.family = None
        self.family_label = ""
        self.maps = []
        self.selected_maps = []
        self.selected_stages = []
        self.page = 0
        self.stage_page = 0
        self.refresh()

    async def initialize(self, interaction):
        try:
            self.metadata = await _stage_metadata()
            self.maps = []
        except Exception:
            await interaction.response.send_message("❌ イベントステージ一覧の取得に失敗しました。", ephemeral=True)
            return
        self.refresh()
        await interaction.response.send_message(
            embed=discord.Embed(
                title="🎪 イベントステージ詳細指定",
                description=(
                    "種別を選択 → マップ一覧を複数選択 → ステージ一覧を選択 → "
                    "クリア回数を入力。"
                ),
                color=0x38bdf8,
            ),
            view=self,
            ephemeral=True,
        )

    def refresh(self):
        self.clear_items()
        self.add_item(EventFamilySelect(self))
        self.add_item(EventMapSelect(self))
        self.add_item(EventStageSelect(self))
        self.add_item(EventFinishButton(self))
        if len(self.maps) > 25:
            self.add_item(_PagerButton(self, -1))
            self.add_item(_PagerButton(self, 1))
        if len([1 for m in self.maps if int(m["id"]) in self.selected_maps for _ in m.get("stages", [])]) > 25:
            self.add_item(_StagePagerButton(self, -1))
            self.add_item(_StagePagerButton(self, 1))


class EventDetailModal:
    def __init__(self, parent_view=None):
        self.parent_view = parent_view

    async def open(self, interaction):
        view = EventDetailView(self.parent_view)
        await view.initialize(interaction)


async def _detail_key_to_parent(interaction,key,label,parent_view=None):
    mode=getattr(parent_view,'payment_mode','yen') if parent_view is not None else 'yen'
    if parent_view is not None and hasattr(parent_view,"selected"):
        parent_view.selected.add(key)
        await interaction.response.send_message(f"✅ {label} を追加しました。注文パネルに戻って購入してください。",ephemeral=True)
    else:
        price=get_point_price(key,interaction.guild_id or 0) if mode=='points' else get_price(key,interaction.guild_id or 0)
        unit='pt' if mode=='points' else '円'
        await interaction.response.send_message(embed=discord.Embed(title='🛒 詳細指定確認',description=f'・{label} — {price}{unit}',color=0xf5c542 if mode=='points' else 0x38bdf8),view=VipConfirmView([key],payment_mode=mode),ephemeral=True)

# DiscordのSelectは1個25項目までなので、グループごとに分ける。
class VipOptionSelect(ui.Select):
    def __init__(self, group_name: str, guild_id: int, payment_mode: str = "yen"):
        self.group_name = group_name
        self.payment_mode = payment_mode
        opts = []
        for label, key in VIP_GROUPS[group_name]:
            mapped = VIP_OPTION_MAP.get(key)
            if not mapped or mapped not in ITEM_CONFIG:
                continue
            price = get_price(mapped, guild_id)
            opts.append(
                discord.SelectOption(
                    label=label[:100],
                    value=key,
                    description=(f"{get_point_price(mapped, guild_id)}pt" if self.payment_mode == "points" else f"{price}円")
                )
            )
        super().__init__(
            placeholder=f"▼ {group_name}を選択",
            min_values=1,
            max_values=min(len(opts), 25),
            options=opts,
            row={"リソース・チケット・ステージ系": 0, "キャラ・施設・その他系①": 1, "キャラ・施設・その他系②": 2}.get(group_name, 0),
        )

    async def callback(self, interaction: discord.Interaction):
        if "dojo_score_detailed" in self.values:
            normal=[v for v in self.values if v != "dojo_score_detailed"]
            if normal:
                selected=[VIP_OPTION_MAP.get(v,v) for v in normal]
                mode=getattr(self,"payment_mode","yen")
                if mode=="points":
                    desc="\n".join(f"・{ITEM_CONFIG[k]['label']} — {get_point_price(k,interaction.guild_id or 0)}pt" for k in selected)+f"\n\n**合計：{sum(get_point_price(k,interaction.guild_id or 0) for k in selected)}pt**"
                    await interaction.response.send_message(embed=discord.Embed(title="🛒 ポイント注文確認",description=desc,color=0xf5c542),view=VipConfirmView(selected,payment_mode="points"),ephemeral=True)
                else:
                    desc="\n".join(f"・{ITEM_CONFIG[k]['label']} — {get_price(k,interaction.guild_id)}円" for k in selected)+f"\n\n**合計：{sum(get_price(k,interaction.guild_id) for k in selected)}円**"
                    await interaction.response.send_message(embed=discord.Embed(title="🛒 VIP注文確認",description=desc,color=0x38bdf8),view=VipConfirmView(selected),ephemeral=True)
                return
            await interaction.response.send_modal(DojoScoreModal())
            return
        detail_map = {
            "legend_detail": LegendDetailModal,
            "event_detail": EventDetailModal,
            "main_stage_detail": MainStageDetailModal,
            "special_stage_detail": SpecialStageDetailModal,
            "ototo_detail": OtotoDetailModal,
            "lineup_custom": LineupDetailModal,
            "labyrinth_detail": LabyrinthDetailModal,
            "facility_detail": FacilityDetailModal,
            "talent_orb_detail": TalentOrbDetailModal,
            "event_ticket_detail": EventTicketDetailModal,
        }
        for detail_key in detail_map:
            if detail_key in self.values:
                normal=[v for v in self.values if v != detail_key]
                selected=[VIP_OPTION_MAP.get(v,v) for v in normal]
                if selected:
                    mode=getattr(self,"payment_mode","yen")
                    if mode=="points":
                        desc="\n".join(f"・{ITEM_CONFIG[k]['label']} — {get_point_price(k,interaction.guild_id or 0)}pt" for k in selected)+f"\n\n**合計：{sum(get_point_price(k,interaction.guild_id or 0) for k in selected)}pt**"
                        await interaction.response.send_message(embed=discord.Embed(title="🛒 ポイント注文確認",description=desc,color=0xf5c542),view=VipConfirmView(selected,payment_mode="points"),ephemeral=True)
                    else:
                        desc="\n".join(f"・{ITEM_CONFIG[k]['label']} — {get_price(k,interaction.guild_id)}円" for k in selected)+f"\n\n**合計：{sum(get_price(k,interaction.guild_id) for k in selected)}円**"
                        await interaction.response.send_message(embed=discord.Embed(title="🛒 VIP注文確認",description=desc,color=0x38bdf8),view=VipConfirmView(selected),ephemeral=True)
                    return
                await detail_map[detail_key](parent_view=self.view).open(interaction)
                return

        if "future_score_individual" in self.values:
            await interaction.response.send_message(
                embed=discord.Embed(title="📊 未来編スコア個別指定", description="未来編1〜3章から**複数選択**し、ステージスロットから全48ステージのスコアを個別に指定できます。\n\n各ステージごとにスコアを入力する方式です。", color=0x38bdf8),
                view=FutureScoreIndividualView(payment_mode=self.payment_mode), ephemeral=True)
            return
        if "future_score_random" in self.values:
            await interaction.response.send_message(
                embed=discord.Embed(
                    title="🎲 未来編スコアランダム",
                    description="未来編1〜3章から**複数選択**できます。選択した章について、日本→月の**全48ステージを1ステージずつ独立して3,000〜9,999でランダム抽選**します。",
                    color=0xf59e0b,
                ),
                view=FutureScoreChapterView(payment_mode=self.payment_mode), ephemeral=True)
            return
        # 未来編スコアは「指定キャラサービス」と同じく、まずサービス内の章を選択してから数値を入力。
        if "future_score_detailed" in self.values:
            normal_values = [v for v in self.values if v != "future_score_detailed"]
            if normal_values:
                selected = [VIP_OPTION_MAP[v] for v in normal_values]
                view = FutureScoreChapterView(selected, payment_mode=self.payment_mode)
                await interaction.response.send_message(
                    embed=discord.Embed(
                        title="📊 未来編 採点スコア指定",
                        description="サービス選択で**未来編1章・2章・3章**から対象の章を選び、次にスコアを入力してください。\n\n※vip.htmlと同じく内部では未来編1〜3章をそれぞれ保存対象として扱います。",
                        color=0x38bdf8,
                    ),
                    view=view, ephemeral=True,
                )
                return
            await interaction.response.send_message(
                embed=discord.Embed(
                    title="📊 未来編 採点スコア指定",
                    description="サービス選択で対象の章を選んでください。\n\n**未来編1章／未来編2章／未来編3章**から選択できます。",
                    color=0x38bdf8,
                ),
                view=FutureScoreChapterView([]), ephemeral=True,
            )
            return

        selected = [VIP_OPTION_MAP[v] for v in self.values]
        await interaction.response.send_message(
            embed=discord.Embed(
                title="🛒 VIP注文確認",
                description="\n".join(
                    f"・{custom_amount_label(*parse_custom_amount_key(k))} — {get_price(k, interaction.guild_id)}円" if parse_custom_amount_key(k) else (f"・{future_score_label(k)} — {get_price(k, interaction.guild_id)}円" if isinstance(k, str) and k.startswith("future_score|") else f"・{ITEM_CONFIG[k]['label']} — {get_price(k, interaction.guild_id)}円")
                    for k in selected
                ) + f"\n\n**合計：{sum(get_price(k, interaction.guild_id) for k in selected)}円**",
                color=0x38bdf8,
            ),
            view=VipConfirmView(selected, payment_mode=getattr(self, "payment_mode", "yen")),
            ephemeral=True,
        )


class FutureScoreChapterSelect(ui.Select):
    def __init__(self, parent_view):
        self.parent_view = parent_view
        super().__init__(
            placeholder="章を選択（1〜3章）",
            min_values=1, max_values=3, row=0,
            options=[
                discord.SelectOption(label="未来編1章", value="3", description="未来編1章・全48ステージ"),
                discord.SelectOption(label="未来編2章", value="4", description="未来編2章・全48ステージ"),
                discord.SelectOption(label="未来編3章", value="5", description="未来編3章・全48ステージ"),
            ],
        )

    async def callback(self, interaction: discord.Interaction):
        self.parent_view.chapters = [int(v) for v in self.values]
        labels = {3: "未来編1章", 4: "未来編2章", 5: "未来編3章"}
        await interaction.response.edit_message(
            embed=discord.Embed(
                title="📊 未来編 採点スコア指定",
                description="選択中：" + "、".join(labels[c] for c in self.parent_view.chapters) + "\n\n下の「スコアを入力」から章ごとのスコアを設定できます。",
                color=0x38bdf8,
            ),
            view=self.parent_view,
        )


class FutureScoreIndividualChapterSelect(ui.Select):
    def __init__(self, parent_view):
        self.parent_view = parent_view
        super().__init__(
            placeholder="章を選択（1〜3章・複数選択可）",
            min_values=1, max_values=3, row=0,
            options=[
                discord.SelectOption(label="未来編1章", value="3", description="全48ステージを個別指定"),
                discord.SelectOption(label="未来編2章", value="4", description="全48ステージを個別指定"),
                discord.SelectOption(label="未来編3章", value="5", description="全48ステージを個別指定"),
            ],
        )

    async def callback(self, interaction: discord.Interaction):
        self.parent_view.chapters = [int(v) for v in self.values]
        self.parent_view.page = 0
        self.parent_view._rebuild_items()
        await interaction.response.edit_message(embed=self.parent_view.build_embed(), view=self.parent_view)


class FutureScoreStageSelect(ui.Select):
    def __init__(self, parent_view):
        self.parent_view = parent_view
        start = parent_view.page * 24
        end = min(start + 24, 48)
        options = []
        for stage in range(start, end):
            done = sum(1 for c in parent_view.chapters if stage + 1 in parent_view.scores.get(c, {}))
            options.append(discord.SelectOption(
                label=f"ステージ{stage + 1:02d}", value=str(stage + 1),
                description=f"選択章 {done}/{len(parent_view.chapters)}件入力済み" if parent_view.chapters else "先に章を選択",
            ))
        super().__init__(placeholder="スコアを設定するステージを選択", min_values=1, max_values=1, options=options, row=1)

    async def callback(self, interaction: discord.Interaction):
        if not self.parent_view.chapters:
            await interaction.response.send_message("❌ 先に未来編1〜3章を選択してください。", ephemeral=True)
            return
        self.parent_view.stage = int(self.values[0])
        await interaction.response.send_modal(FutureScoreIndividualModal(self.parent_view))


class FutureScoreIndividualModal(ui.Modal):
    def __init__(self, parent_view):
        super().__init__(title=f"未来編ステージ{parent_view.stage:02d} スコア入力", timeout=300)
        self.parent_view = parent_view
        self.field = ui.TextInput(label="スコア（0〜9,999）", placeholder="例：9999", required=True, max_length=4)
        self.add_item(self.field)

    async def on_submit(self, interaction: discord.Interaction):
        try:
            score = int(self.field.value.strip())
            if not 0 <= score <= 9999:
                raise ValueError
        except ValueError:
            await interaction.response.send_message("❌ スコアは0〜9,999で指定してください。", ephemeral=True)
            return
        for chapter in self.parent_view.chapters:
            self.parent_view.scores.setdefault(chapter, {})[self.parent_view.stage] = score
        self.parent_view._rebuild_items()
        await interaction.response.edit_message(embed=self.parent_view.build_embed(), view=self.parent_view)


class FutureScoreIndividualPrevButton(ui.Button):
    def __init__(self, parent_view):
        self.parent_view = parent_view
        super().__init__(label="◀ 前半", style=discord.ButtonStyle.secondary, row=2)
    async def callback(self, interaction: discord.Interaction):
        self.parent_view.page = 0
        self.parent_view._rebuild_items()
        await interaction.response.edit_message(embed=self.parent_view.build_embed(), view=self.parent_view)


class FutureScoreIndividualNextButton(ui.Button):
    def __init__(self, parent_view):
        self.parent_view = parent_view
        super().__init__(label="後半 ▶", style=discord.ButtonStyle.secondary, row=2)
    async def callback(self, interaction: discord.Interaction):
        self.parent_view.page = 1
        self.parent_view._rebuild_items()
        await interaction.response.edit_message(embed=self.parent_view.build_embed(), view=self.parent_view)


class FutureScoreIndividualConfirmButton(ui.Button):
    def __init__(self, parent_view):
        self.parent_view = parent_view
        super().__init__(label="🛒 この内容で進む", style=discord.ButtonStyle.success, row=2)
    async def callback(self, interaction: discord.Interaction):
        if not self.parent_view.chapters:
            await interaction.response.send_message("❌ 対象の章を1つ以上選択してください。", ephemeral=True)
            return
        missing = [c for c in self.parent_view.chapters if len(self.parent_view.scores.get(c, {})) < 48]
        if missing:
            labels = {3: "未来編1章", 4: "未来編2章", 5: "未来編3章"}
            await interaction.response.send_message("❌ 選択した章の48ステージすべてにスコアを入力してください。未完了：" + "、".join(labels[c] for c in missing), ephemeral=True)
            return
        keys = [f"future_score_individual|{c}|{json.dumps(self.parent_view.scores[c], ensure_ascii=False, separators=(',', ':'))}" for c in self.parent_view.chapters]
        if self.parent_view.new_account_view is not None:
            self.parent_view.new_account_view.selected.update(keys)
            await interaction.response.edit_message(
                embed=self.parent_view.new_account_view.build_embed(interaction.guild_id or 0),
                view=self.parent_view.new_account_view,
            )
            return
        mode = getattr(self.parent_view, "payment_mode", "yen")
        if mode == "points":
            total = sum(get_point_price(k, interaction.guild_id or 0) for k in keys)
            desc = "\n".join(f"・{future_score_individual_label(k)} — {get_point_price(k, interaction.guild_id or 0)}pt" for k in keys)
            await interaction.response.send_message(embed=discord.Embed(title="🛒 ポイント注文確認", description=desc + f"\n\n**合計：{total}pt**", color=0xf5c542), view=VipConfirmView(keys, payment_mode="points"), ephemeral=True)
        else:
            total = sum(get_price(k, interaction.guild_id) for k in keys)
            desc = "\n".join(f"・{future_score_individual_label(k)} — {get_price(k, interaction.guild_id)}円" for k in keys)
            await interaction.response.send_message(embed=discord.Embed(title="🛒 VIP注文確認", description=desc + f"\n\n**合計：{total}円**", color=0x38bdf8), view=VipConfirmView(keys), ephemeral=True)


class FutureScoreIndividualView(ui.View):
    def __init__(self, new_account_view=None, payment_mode: str = "yen"):
        super().__init__(timeout=600)
        self.new_account_view = new_account_view
        self.payment_mode = payment_mode
        self.chapters = []
        self.scores = {3: {}, 4: {}, 5: {}}
        self.page = 0
        self.stage = None
        self._rebuild_items()
    def _rebuild_items(self):
        self.clear_items()
        self.add_item(FutureScoreIndividualChapterSelect(self))
        if self.chapters:
            self.add_item(FutureScoreStageSelect(self))
        self.add_item(FutureScoreIndividualPrevButton(self))
        self.add_item(FutureScoreIndividualNextButton(self))
        self.add_item(FutureScoreIndividualConfirmButton(self))
    def build_embed(self):
        labels = {3: "未来編1章", 4: "未来編2章", 5: "未来編3章"}
        progress = "・章未選択" if not self.chapters else "\n".join(f"・{labels[c]}：{len(self.scores.get(c, {}))}/48ステージ入力済み" for c in self.chapters)
        return discord.Embed(title="📊 未来編スコア個別指定", description=("① 未来編1〜3章から複数選択\n② ステージスロットから選択\n③ スコアを入力\n\n" + progress + "\n\nステージ01〜24／25〜48をページ切替で選択できます。"), color=0x38bdf8)


def future_score_individual_label(key: str) -> str:
    try:
        _, chapter, payload = key.split("|", 2)
        names = {"3": "未来編1章", "4": "未来編2章", "5": "未来編3章"}
        scores = json.loads(payload)
        return f"{names.get(chapter, '未来編')} スコア個別指定（全{len(scores)}ステージ）"
    except Exception:
        return "未来編スコア個別指定"


class FutureScoreInputModal(ui.Modal):
    def __init__(self, parent_view):
        super().__init__(title="未来編 採点スコア入力", timeout=300)
        self.parent_view = parent_view
        labels = {3: "未来編1章", 4: "未来編2章", 5: "未来編3章"}
        self.inputs = []
        for chapter in parent_view.chapters:
            field = ui.TextInput(
                label=f"{labels[chapter]}のスコア",
                placeholder="0〜9999（例：9999）",
                required=True, max_length=4,
            )
            self.inputs.append((chapter, field))
            self.add_item(field)

    async def on_submit(self, interaction: discord.Interaction):
        scores = {}
        for chapter, field in self.inputs:
            try:
                score = int(field.value.strip())
            except ValueError:
                await interaction.response.send_message("❌ スコアは数字で入力してください。", ephemeral=True)
                return
            if not 0 <= score <= 9999:
                await interaction.response.send_message("❌ スコアは0〜9,999で指定してください。", ephemeral=True)
                return
            scores[chapter] = score
        self.parent_view.random_mode = False
        self.parent_view.scores = scores
        await interaction.response.edit_message(
            embed=self.parent_view.build_embed(),
            view=self.parent_view,
        )


class FutureScoreChapterView(ui.View):
    def __init__(self, base_items=None, new_account_view=None):
        super().__init__(timeout=300)
        self.base_items = list(base_items or [])
        self.new_account_view = new_account_view
        self.chapters = []
        self.scores = {}
        self.random_mode = False
        self.add_item(FutureScoreChapterSelect(self))
        self.add_item(FutureScoreInputButton(self))
        self.add_item(FutureScoreRandomButton(self))
        self.add_item(FutureScoreConfirmButton(self))

    def build_embed(self):
        labels = {3: "未来編1章", 4: "未来編2章", 5: "未来編3章"}
        if not self.chapters:
            text = "・章未選択"
        else:
            if self.random_mode:
                text = "\n".join(
                    f"・{labels[c]}：日本→月の全48ステージを個別ランダム済み"
                    for c in self.chapters
                )
            else:
                text = "\n".join(f"・{labels[c]}：{self.scores.get(c, '未入力')}" for c in self.chapters)
        mode_text = "🎲 ランダム：各ステージを3,000〜9,999で個別抽選" if self.random_mode else "✏️ 手動指定：章全体に0〜9,999"
        return discord.Embed(
            title="📊 未来編 採点スコア指定",
            description=f"対象章\n{text}\n\n{mode_text}",
            color=0x38bdf8,
        )


class FutureScoreInputButton(ui.Button):
    def __init__(self, parent_view):
        self.parent_view = parent_view
        super().__init__(label="✏️ スコアを入力", style=discord.ButtonStyle.secondary, row=1)

    async def callback(self, interaction: discord.Interaction):
        if not self.parent_view.chapters:
            await interaction.response.send_message("❌ 先に未来編1〜3章から対象の章を選択してください。", ephemeral=True)
            return
        await interaction.response.send_modal(FutureScoreInputModal(self.parent_view))


class FutureScoreRandomButton(ui.Button):
    def __init__(self, parent_view):
        self.parent_view = parent_view
        super().__init__(label="🎲 ランダム設定", style=discord.ButtonStyle.primary, row=1)

    async def callback(self, interaction: discord.Interaction):
        if not self.parent_view.chapters:
            await interaction.response.send_message("❌ 先に未来編1〜3章から対象の章を選択してください。", ephemeral=True)
            return
        # 章ごとに1個の値を入れるのではなく、各章の「日本」から「月」まで全48ステージを
        # それぞれ独立して3,000〜9,999でランダム生成する。
        # 例：1章なら [3468, 7210, 4051, ...] のように48個すべて別抽選。
        self.parent_view.random_mode = True
        self.parent_view.scores = {
            chapter: [random.randint(3000, 9999) for _ in range(48)]
            for chapter in self.parent_view.chapters
        }
        await interaction.response.edit_message(
            embed=self.parent_view.build_embed(),
            view=self.parent_view,
        )


class FutureScoreConfirmButton(ui.Button):
    def __init__(self, parent_view):
        self.parent_view = parent_view
        super().__init__(label="🛒 この内容で進む", style=discord.ButtonStyle.success, row=1)

    async def callback(self, interaction: discord.Interaction):
        if not self.parent_view.chapters:
            await interaction.response.send_message("❌ 対象の章を1つ以上選択してください。", ephemeral=True)
            return
        if any(c not in self.parent_view.scores for c in self.parent_view.chapters):
            await interaction.response.send_message("❌ 選択した章のスコアをすべて入力してください。", ephemeral=True)
            return
        if self.parent_view.random_mode:
            # ランダム設定時は、各章の48ステージ分の値をそのまま注文データへ渡す。
            # ここでは再抽選せず、確認画面で確定した乱数を代行側でも同じ値として扱う。
            score_keys = [
                f"future_score|{c}|random:{json.dumps(self.parent_view.scores[c], ensure_ascii=False, separators=(',', ':'))}"
                for c in self.parent_view.chapters
            ]
        else:
            score_keys = [f"future_score|{c}|{self.parent_view.scores[c]}" for c in self.parent_view.chapters]
        selected = self.parent_view.base_items + score_keys
        if self.parent_view.new_account_view is not None:
            self.parent_view.new_account_view.selected.update(selected)
            await interaction.response.edit_message(
                embed=self.parent_view.new_account_view.build_embed(interaction.guild_id or 0),
                view=self.parent_view.new_account_view,
            )
            return
        total = sum(get_price(k, interaction.guild_id) for k in selected)
        await interaction.response.send_message(
            embed=discord.Embed(
                title="🛒 VIP注文確認",
                description="\n".join(f"・{future_score_label(k) if k.startswith('future_score|') else ITEM_CONFIG[k]['label']} — {get_price(k, interaction.guild_id)}円" for k in selected) + f"\n\n**合計：{total}円**",
                color=0x38bdf8,
            ),
            view=VipConfirmView(selected), ephemeral=True,
        )


def future_score_label(key: str) -> str:
    try:
        _, chapter, score = key.split("|", 2)
        names = {"3": "未来編1章", "4": "未来編2章", "5": "未来編3章"}
        name = names.get(chapter, "未来編")
        if score.startswith("random:"):
            values = json.loads(score[len("random:"):])
            return f"{name} 採点スコア（日本→月・全48ステージ個別ランダム）"
        return f"{name} 採点スコア {int(score):,}"
    except Exception:
        return "未来編 採点スコア指定"


class VipConfirmView(ui.View):
    def __init__(self, selected: list[str], payment_mode: str = "yen"):
        super().__init__(timeout=300)
        self.selected = list(selected)
        self.payment_mode = payment_mode

    def reset_custom_amounts(self):
        # 注文成功後は指定個数の「種類|数量」だけを消す。
        # 通常サービスの選択まで消さない。
        self.selected = [k for k in self.selected if not parse_custom_amount_key(k)]

    @ui.button(label="🛒 購入する", style=discord.ButtonStyle.success)
    async def buy(self, interaction: discord.Interaction, button: ui.Button):
        if self.payment_mode == "points":
            total = sum(get_point_price(k, interaction.guild_id or 0) for k in self.selected)
            if total <= 0:
                await interaction.response.send_modal(FreeModal(self.selected, self))
            else:
                await interaction.response.send_modal(PointPurchaseModal(self.selected, total, self))
            return
        total = sum(get_price(k, interaction.guild_id) for k in self.selected)
        if total <= 0:
            await interaction.response.send_modal(FreeModal(self.selected, self))
        else:
            await interaction.response.send_modal(PurchaseModal(self.selected, total, self))


class PointToolsView(ui.View):
    def __init__(self):
        super().__init__(timeout=300)
        self.add_item(PointInviteButton())
        self.add_item(PointBalanceButton())
        self.add_item(PointAuthButton())

class PointInviteButton(ui.Button):
    def __init__(self):
        super().__init__(label="🎁 招待リンクを発行",style=discord.ButtonStyle.success)
    async def callback(self,interaction):
        guild=interaction.guild
        if guild is None or interaction.channel is None:
            await interaction.response.send_message('❌ サーバー内のチャンネルで実行してください。',ephemeral=True); return
        gid=int(guild.id); uid=int(interaction.user.id); invite=None; stored_code=None; could_list_invites=True
        # 既存の専用リンクがまだ有効なら再利用する（ボタン連打で新規リンクを量産させない）。
        try:
            with _POINT_DB_LOCK:
                conn=_point_db()
                row=conn.execute('SELECT invite_code FROM point_invites WHERE guild_id=? AND inviter_id=? ORDER BY created_at DESC LIMIT 1',(gid,uid)).fetchone()
                conn.close()
            if row:
                stored_code=str(row['invite_code'])
                try:
                    invite=next((x for x in await guild.invites() if x.code==stored_code),None)
                except Exception:
                    could_list_invites=False
        except Exception:
            could_list_invites=False
        if stored_code and invite is None and not could_list_invites:
            # 招待一覧を読めないときも新規作成せず、保存済みリンクを返す。
            invite_url=f'https://discord.gg/{stored_code}'
            await interaction.response.send_message(f'🎁 **あなた専用の招待リンク（保存済み）**\n{invite_url}\n\n既存リンクを再利用しました。Botに「招待を管理」権限がないため、有効性確認はできません。新しいリンクは発行していません。',ephemeral=True)
            return
        if invite is None:
            try:
                invite=await interaction.channel.create_invite(max_age=0,max_uses=0,unique=True,reason=f'ポイント招待:{uid}')
            except Exception as e:
                await interaction.response.send_message(f'❌ 招待リンクを作成できませんでした。Botに招待作成権限と招待一覧の閲覧権限があるか確認してください。\n```{str(e)[:200]}```',ephemeral=True); return
            with _POINT_DB_LOCK:
                conn=_point_db()
                conn.execute('INSERT OR REPLACE INTO point_invites(guild_id,inviter_id,invite_code,created_at) VALUES(?,?,?,?)',(gid,uid,invite.code,_point_now().isoformat()))
                conn.commit(); conn.close()
        _POINT_INVITE_CACHE[(gid,invite.code)]=(uid,int(invite.uses or 0))
        await interaction.response.send_message(f'🎁 **あなた専用の招待リンク（同じリンクを再利用）**\n{invite.url}\n\n発行ボタンをもう一度押しても、このリンクを再表示します。\n紹介報酬は対象ユーザー・UDIDごとに重複付与されません。条件を満たすと **+{POINT_INVITE_REWARD}pt** です。',ephemeral=True)

class PointBalanceButton(ui.Button):
    def __init__(self): super().__init__(label="💰 ポイント確認",style=discord.ButtonStyle.primary)
    async def callback(self,interaction):
        gid=interaction.guild_id or 0; bal=_point_get(gid,interaction.user.id); rows=_point_history(gid,interaction.user.id,8)
        hist='\n'.join(f"{'+' if int(r['delta'])>0 else ''}{int(r['delta'])}pt｜{r['reason']}" for r in rows) or '履歴なし'
        await interaction.response.send_message(embed=discord.Embed(title='💰 ポイント',description=f'残高：**{bal:,}pt**\n\n{hist}',color=0x00cc88),ephemeral=True)

class PointAuthButton(ui.Button):
    def __init__(self): super().__init__(label="📱 端末認証",style=discord.ButtonStyle.secondary)
    async def callback(self,interaction):
        if not POINT_UDID_WEB_URL:
            await interaction.response.send_message('❌ POINT_UDID_WEB_URL が未設定です。',ephemeral=True); return
        token=_point_create_auth_token(interaction.guild_id or 0,interaction.user.id)
        if not token:
            await interaction.response.send_message("❌ POINT_UDID_SHARED_SECRET が未設定です。",ephemeral=True); return
        sep='&' if '?' in POINT_UDID_WEB_URL else '?'
        url=f"{POINT_UDID_WEB_URL}{sep}token={urllib.parse.quote(token)}"
        await interaction.response.send_message(f"📱 **端末認証URL**\n{url}\n\n15分で期限切れになります。",ephemeral=True)

class PointToolsButton(ui.Button):
    def __init__(self):
        super().__init__(label="🎁 ポイント・招待",style=discord.ButtonStyle.secondary,row=3)
    async def callback(self,interaction):
        await interaction.response.send_message(embed=discord.Embed(title='💰 ポイント・招待',description='招待リンク発行、ポイント確認、端末認証ができます。',color=0xf5c542),view=PointToolsView(),ephemeral=True)

class VipPanelView(ui.View):
    def __init__(self, guild_id: int = 0, payment_mode: str = "yen"):
        super().__init__(timeout=None)
        self.guild_id = guild_id
        self.payment_mode = payment_mode
        for group in VIP_GROUPS:
            self.add_item(VipOptionSelect(group, guild_id, payment_mode))
        self.add_item(VipCharacterButton(payment_mode))
        self.add_item(VipAccountPanelButton(payment_mode))
        if payment_mode == "points":
            self.add_item(PointToolsButton())
        self.add_item(VipCustomSelect(payment_mode))


class VipCharacterButton(ui.Button):
    def __init__(self, payment_mode: str = "yen"):
        self.payment_mode = payment_mode
        super().__init__(
            label="🔎 指定キャラパネル",
            style=discord.ButtonStyle.secondary,
            row=3,
            custom_id="vip_character_panel",
        )

    async def callback(self, interaction: discord.Interaction):
        await interaction.response.send_message(
            embed=discord.Embed(
                title="にゃんこ大戦争 代行自販機",
                description="以下のセレクトから選択して購入してください。\n価格はセレクトメニュー内に表示されます",
                color=0x38bdf8,
            ),
            view=CharaPanelView(interaction.guild_id or 0, payment_mode=self.payment_mode),
            ephemeral=True,
        )


class VipAccountPanelButton(ui.Button):
    def __init__(self, payment_mode: str = "yen"):
        self.payment_mode = payment_mode
        super().__init__(
            label="👤 垢パネル",
            style=discord.ButtonStyle.primary,
            row=3,
            custom_id="vip_account_panel",
        )

    async def callback(self, interaction: discord.Interaction):
        await interaction.response.send_message(
            embed=discord.Embed(
                title="👤 アカウントパネル",
                description="初期垢・初心者垢・中級者垢・上級者垢をここから選択できます。",
                color=0x5865F2,
            ),
            view=AccountPresetView(interaction.guild_id or 0, payment_mode=self.payment_mode),
            ephemeral=True,
        )


NEW_ACCOUNT_TYPES = (
    ("new", "初期垢"),
    ("beginner", "初心者垢"),
    ("intermediate", "中級者垢"),
    ("advanced", "上級者垢"),
)

class NewAccountTypeSelect(ui.Select):
    def __init__(self):
        super().__init__(
            placeholder="① アカウント種別を選択",
            min_values=1, max_values=1, row=0,
            options=[discord.SelectOption(label=label, value=key) for key, label in NEW_ACCOUNT_TYPES],
            custom_id="new_account_type_select",
        )
    async def callback(self, interaction: discord.Interaction):
        key = self.values[0]
        label = dict(NEW_ACCOUNT_TYPES)[key]
        await interaction.response.send_message(
            embed=discord.Embed(
                title=f"👤 {label}（新規垢）",
                description=(
                    "この種別を選択しました。\n"
                    "下の項目からVIP.htmlの新規作成欄＋にゃんこパネルの通常サービスを選択できます。\n"
                    "猫缶・XP・チケット等は固定値ではなく『指定個数』から入力してください。"
                ), color=0x5865F2),
            view=NewAccountOrderView(interaction.guild_id or 0, key, label),
            ephemeral=True,
        )

class NewAccountOptionSelect(ui.Select):
    def __init__(self, group_name: str, guild_id: int):
        self.group_name = group_name
        opts=[]
        for label, key in NEW_ACCOUNT_GROUPS[group_name]:
            mapped = VIP_OPTION_MAP.get(key)
            supported = bool(mapped and mapped in ITEM_CONFIG)
            opts.append(discord.SelectOption(
                label=label[:100], value=key,
                description=(f"{get_price(mapped, guild_id)}円" if supported else "詳細指定/新規垢バックエンド対応待ち")[:100]
            ))
        super().__init__(placeholder=f"▼ {group_name}を選択", min_values=1,
                         max_values=min(25,len(opts)), options=opts,
                         row=1 if group_name=="アイテム・ステージ" else 2 if group_name=="システム・ガマトト" else 3,
                         custom_id=f"new_account_group_{group_name}")
    async def callback(self, interaction: discord.Interaction):
        view = self.view
        if not isinstance(view, NewAccountOrderView):
            await interaction.response.defer()
            return

        values = list(self.values)
        detail_map = {
            "legend_detail": LegendDetailModal,
            "event_detail": EventDetailModal,
            "main_stage_detail": MainStageDetailModal,
            "special_stage_detail": SpecialStageDetailModal,
            "ototo_detail": OtotoDetailModal,
            "lineup_custom": LineupDetailModal,
            "labyrinth_detail": LabyrinthDetailModal,
            "facility_detail": FacilityDetailModal,
            "talent_orb_detail": TalentOrbDetailModal,
            "event_ticket_detail": EventTicketDetailModal,
        }
        for detail_key, modal_cls in detail_map.items():
            if detail_key in values:
                normal_values=[v for v in values if v != detail_key]
                view.selected.update(normal_values)
                await modal_cls(view).open(interaction)
                return
        # 未来編スコア系は専用UIで設定してから新規垢側へ戻す.
        if "future_score_individual" in values:
            normal_values = [v for v in values if v != "future_score_individual"]
            view.selected.update(normal_values)
            await interaction.response.send_message(
                embed=discord.Embed(
                    title="📊 未来編スコア個別指定（新規垢）",
                    description="未来編1〜3章を選択し、全48ステージのスコアを個別に入力します。",
                    color=0x38bdf8,
                ),
                view=FutureScoreIndividualView(new_account_view=view),
                ephemeral=True,
            )
            return

        if "future_score_random" in values:
            normal_values = [v for v in values if v != "future_score_random"]
            view.selected.update(normal_values)
            await interaction.response.send_message(
                embed=discord.Embed(
                    title="🎲 未来編スコアランダム（新規垢）",
                    description="未来編1〜3章を選択し、各章48ステージを3,000〜9,999で個別ランダム設定します。",
                    color=0xf59e0b,
                ),
                view=FutureScoreChapterView([], new_account_view=view),
                ephemeral=True,
            )
            return

        if "future_score_detailed" in values:
            normal_values = [v for v in values if v != "future_score_detailed"]
            view.selected.update(normal_values)
            await interaction.response.send_message(
                embed=discord.Embed(
                    title="📊 未来編 採点スコア指定（新規垢）",
                    description="未来編1〜3章から対象章を選び、章ごとのスコアを入力します。",
                    color=0x38bdf8,
                ),
                view=FutureScoreChapterView([], new_account_view=view),
                ephemeral=True,
            )
            return

        if "dojo_score_detailed" in values:
            normal_values = [v for v in values if v != "dojo_score_detailed"]
            view.selected.update(normal_values)
            await interaction.response.send_modal(NewAccountDojoScoreModal(view))
            return

        view.selected.update(values)
        await interaction.response.edit_message(embed=view.build_embed(interaction.guild_id or 0), view=view)

NEW_ACCOUNT_CHARA_SERVICES = [
    ("chara_unlock", "指定キャラ解放"),
    ("chara_delete", "指定キャラ削除"),
    ("chara_lvmax_plus", "指定キャラLv.Max+"),
    ("chara_lvmax", "指定キャラLv.Max"),
    ("chara_form", "指定キャラ最終形態化"),
    ("chara_level_plus", "指定キャラLv／＋値指定"),
    ("chara_form_select", "指定キャラ形態指定"),
    ("chara_talents", "指定キャラ本能設定"),
]

class NewAccountCharaSelect(ui.Select):
    def __init__(self, guild_id: int):
        options=[]
        for key, label in NEW_ACCOUNT_CHARA_SERVICES:
            cfg=CHARA_CONFIG[key]
            price=get_special_price(cfg["price_key"], cfg["default"], guild_id)
            options.append(discord.SelectOption(label=label, value=key, description=f"{price}円"))
        super().__init__(placeholder="③ 指定キャラサービスを選択", min_values=1, max_values=1,
                         options=options, row=3, custom_id="new_account_chara_service")

    async def callback(self, interaction: discord.Interaction):
        key=self.values[0]
        cfg=CHARA_CONFIG[key]
        await interaction.response.send_modal(NewAccountCharaModal(key, cfg["label"], self.view))

class NewAccountCharaModal(ui.Modal):
    def __init__(self, key: str, label: str, parent_view):
        super().__init__(title=f"新規垢｜{label}", timeout=300)
        self.key = key
        self.label = label
        self.parent_view = parent_view
        self.ids = ui.TextInput(
            label="キャラクターID",
            placeholder="例: 1, 5, 12, 98（複数はカンマ区切り）",
            required=True, max_length=500
        )
        self.add_item(self.ids)

        # ID入力欄の下に、必要なサービスだけ追加項目を表示する。
        if key == "chara_level_plus":
            self.level = ui.TextInput(
                label="レベル（1～60）",
                placeholder="例: 50",
                required=True, max_length=2
            )
            self.plus = ui.TextInput(
                label="＋値（0～90）",
                placeholder="例: 20",
                required=True, max_length=2
            )
            self.add_item(self.level)
            self.add_item(self.plus)

    @staticmethod
    def _parse_ids(raw: str):
        parts = [x.strip() for x in raw.replace("、", ",").split(",") if x.strip()]
        if not parts or any(not x.isdigit() for x in parts):
            return None
        ids = [int(x) for x in parts]
        if any(x < 1 for x in ids):
            return None
        return ids

    async def on_submit(self, interaction: discord.Interaction):
        ids = self._parse_ids(self.ids.value)
        if not ids:
            await interaction.response.send_message(
                "❌ キャラクターIDは1以上の数字をカンマ区切りで入力してください。",
                ephemeral=True
            )
            return

        # 形態指定はID入力後に1～4のセレクトを出す。
        if self.key == "chara_form_select":
            view = NewAccountFormSelectView(self.parent_view, self.label, ids)
            await interaction.response.send_message(
                "キャラクターIDを受け付けました。指定する形態を1～4から選択してください。",
                view=view,
                ephemeral=True
            )
            return

        detail = {
            "service_key": self.key,
            "label": self.label,
            "ids": ids,
        }

        if self.key == "chara_level_plus":
            try:
                lv = int(self.level.value)
                plus = int(self.plus.value)
            except ValueError:
                await interaction.response.send_message(
                    "❌ レベルと＋値は数字で入力してください。",
                    ephemeral=True
                )
                return
            if not 1 <= lv <= 60 or not 0 <= plus <= 90:
                await interaction.response.send_message(
                    "❌ レベルは1～60、＋値は0～90で指定してください。",
                    ephemeral=True
                )
                return
            detail.update(level=lv, plus=plus)

        # 本能設定は「本能を全て解放」なので、キャラIDだけ受け取る。
        if self.key == "chara_talents":
            detail["talents"] = "all"

        self.parent_view.character_requests.append(detail)
        await interaction.response.edit_message(
            embed=self.parent_view.build_embed(interaction.guild_id or 0),
            view=self.parent_view
        )


class NewAccountFormSelectView(ui.View):
    """指定キャラ形態指定：ID入力後に1～4だけを選ばせる。"""
    def __init__(self, parent_view, label: str, ids):
        super().__init__(timeout=300)
        self.parent_view = parent_view
        self.label = label
        self.ids = ids
        self.add_item(NewAccountFormSelect(self))


class NewAccountFormSelect(ui.Select):
    def __init__(self, parent):
        self.parent_form_view = parent
        options = [
            discord.SelectOption(label=f"{i}形態", value=str(i))
            for i in range(1, 5)
        ]
        super().__init__(
            placeholder="指定する形態を選択",
            min_values=1,
            max_values=1,
            options=options,
            row=0,
        )

    async def callback(self, interaction: discord.Interaction):
        form = int(self.values[0])
        detail = {
            "service_key": "chara_form_select",
            "label": self.parent_form_view.label,
            "ids": self.parent_form_view.ids,
            "form": form,
        }
        self.parent_form_view.parent_view.character_requests.append(detail)
        await interaction.response.edit_message(
            content=f"✅ {', '.join(map(str, self.parent_form_view.ids))} → {form}形態 を追加しました。",
            view=None
        )


class NewAccountCustomSelect(ui.Select):
    def __init__(self):
        super().__init__(placeholder="④ 指定個数（1から自由に入力）", min_values=1, max_values=1,
                         options=[discord.SelectOption(label=label, value=kind, description="個数を自由に指定") for label,kind in VIP_CUSTOM_OPTIONS],
                         row=0, custom_id="new_account_custom_amount")
    async def callback(self, interaction: discord.Interaction):
        kind=self.values[0]
        await interaction.response.send_modal(NewAccountCustomAmountModal(kind, dict((kind, label) for label, kind in VIP_CUSTOM_OPTIONS)[kind], self.view))

class NewAccountCustomAmountModal(ui.Modal):
    def __init__(self, kind: str, label: str, parent_view):
        super().__init__(title=f"{label} 指定個数", timeout=300)
        self.kind=kind; self.parent_view=parent_view
        self.amount=ui.TextInput(label="指定値", placeholder="例: 1000", required=True, max_length=7)
        self.add_item(self.amount)
    async def on_submit(self, interaction: discord.Interaction):
        try: amount=int(self.amount.value.strip())
        except ValueError:
            await interaction.response.send_message("❌ 数字で入力してください。", ephemeral=True); return
        if amount<0 or amount>9_999_999:
            await interaction.response.send_message("❌ 0～9,999,999の範囲で指定してください。", ephemeral=True); return
        key=make_custom_amount_key(self.kind, amount)
        self.parent_view.selected.add(key)
        await interaction.response.edit_message(embed=self.parent_view.build_embed(interaction.guild_id or 0), view=self.parent_view)

class NewAccountDojoScoreModal(ui.Modal):
    def __init__(self, parent_view):
        super().__init__(title="新規垢｜道場スコア指定", timeout=300)
        self.parent_view = parent_view
        self.score = ui.TextInput(
            label="道場・入門の間スコア",
            placeholder="例：999999",
            required=True, max_length=10,
        )
        self.add_item(self.score)

    async def on_submit(self, interaction: discord.Interaction):
        try:
            score = int(self.score.value.strip())
            if not 0 <= score <= 2_147_483_647:
                raise ValueError
        except ValueError:
            await interaction.response.send_message("❌ スコアは0〜2,147,483,647で指定してください。", ephemeral=True)
            return
        self.parent_view.dojo_score_settings = {"hall_of_initiates": score}
        self.parent_view.selected = {k for k in self.parent_view.selected if k != "dojo_score_detailed"}
        self.parent_view.selected.add(f"dojo_score|{score}")
        await interaction.response.edit_message(
            embed=self.parent_view.build_embed(interaction.guild_id or 0),
            view=self.parent_view,
        )


class NewAccountSetupButton(ui.Button):
    def __init__(self):
        # セレクトメニューは各行の幅を5使うため、ボタン類は最下段(row=4)へまとめる。
        super().__init__(label="⚙️ 作成数・設定先", style=discord.ButtonStyle.secondary, row=4)
    async def callback(self, interaction: discord.Interaction):
        if not isinstance(self.view, NewAccountOrderView):
            await interaction.response.defer(); return
        await interaction.response.send_message("作成数と追加アイテムの設定先を選択してください。", view=NewAccountSetupView(self.view), ephemeral=True)

class NewAccountSetupView(ui.View):
    def __init__(self, parent):
        super().__init__(timeout=300)
        self.parent = parent
        self.add_item(NewAccountCountSelect(parent))
        self.add_item(NewAccountTargetSelect(parent))


class NewAccountCountSelect(ui.Select):
    def __init__(self, parent):
        self.parent_order = parent
        count = getattr(parent, "create_count", 1)
        super().__init__(
            placeholder=f"作成数：{count}個",
            min_values=1, max_values=1, row=0,
            options=[discord.SelectOption(label=f"{n}個作成", value=str(n), default=(n == count)) for n in range(1, 6)],
            custom_id="new_account_create_count",
        )

    async def callback(self, interaction: discord.Interaction):
        setup = self.view
        view = self.parent_order
        if not isinstance(setup, NewAccountSetupView) or not isinstance(view, NewAccountOrderView):
            await interaction.response.defer()
            return
        view.create_count = int(self.values[0])
        if view.active_account > view.create_count:
            view.active_account = view.create_count
        view.target_selection = str(view.active_account)
        # 同じViewを再利用せず、現在値をdefault/placeholderへ反映した新しいViewを返す。
        # Discordクライアント側に「前の1個目」の表示が残る問題を防ぐ。
        await interaction.response.edit_message(
            content=f"作成数：{view.create_count}個。設定先：{view.target_selection if view.target_selection != 'all' else '全て'}。",
            view=NewAccountSetupView(view),
        )


class NewAccountTargetSelect(ui.Select):
    def __init__(self, parent):
        self.parent_order = parent
        target = getattr(parent, "target_selection", str(getattr(parent, "active_account", 1)))
        create_count = getattr(parent, "create_count", 1)
        options = [
            discord.SelectOption(label=f"{i}個目", value=str(i), default=(target == str(i)))
            for i in range(1, create_count + 1)
        ]
        options.append(discord.SelectOption(
            label="全て選択",
            description="現在の設定を作成する全アカウントへコピー",
            value="all",
            default=(target == "all"),
        ))
        super().__init__(
            placeholder=("設定先：全て" if target == "all" else f"設定先：{target}個目"),
            min_values=1, max_values=1, row=1,
            options=options,
            custom_id="new_account_target",
        )

    async def callback(self, interaction: discord.Interaction):
        view = self.parent_order
        if not isinstance(view, NewAccountOrderView):
            await interaction.response.defer()
            return
        value = self.values[0]
        if value == "all":
            source = view.account_configs[view.active_account]
            for i in range(1, view.create_count + 1):
                if i == view.active_account:
                    continue
                view.account_configs[i] = {
                    "selected": set(source["selected"]),
                    "character_requests": [dict(x) for x in source["character_requests"]],
                    "dojo_score_settings": dict(source["dojo_score_settings"]) if source["dojo_score_settings"] else None,
                }
            view.target_selection = "all"
        else:
            view.active_account = int(value)
            view.target_selection = value
        await interaction.response.edit_message(
            content=f"作成数：{view.create_count}個。設定先：{'全て' if view.target_selection == 'all' else view.target_selection + '個目'}。",
            view=NewAccountSetupView(view),
        )

class NewAccountCharacterIdSearchButton(ui.Button):
    def __init__(self):
        super().__init__(
            label="🔍 キャラクターID検索",
            style=discord.ButtonStyle.secondary,
            custom_id="new_account_chara_id_search_button",
            row=4,
        )

    async def callback(self, interaction: discord.Interaction):
        await interaction.response.send_modal(CharacterIdSearchModal(self.view))


class NewAccountOrderView(ui.View):
    def __init__(self, guild_id: int, account_type: str, account_label: str, payment_mode: str = "yen"):
        self.payment_mode = payment_mode
        super().__init__(timeout=600)
        self.guild_id=guild_id; self.account_type=account_type; self.account_label=account_label
        self.create_count=1
        self.active_account=1
        self.target_selection="1"
        self.account_configs={i:{"selected":set(),"character_requests":[],"dojo_score_settings":None} for i in range(1,6)}
        self.add_item(NewAccountSetupButton())
        self.add_item(NewAccountOptionSelect("アイテム・ステージ", guild_id))
        self.add_item(NewAccountOptionSelect("システム・ガマトト", guild_id))
        self.add_item(NewAccountCharaSelect(guild_id))
        self.add_item(NewAccountCustomSelect())
        self.add_item(NewAccountCharacterIdSearchButton())
        self.add_item(NewAccountExecuteButton())

    @property
    def selected(self):
        return self.account_configs[self.active_account]["selected"]
    @selected.setter
    def selected(self, value):
        self.account_configs[self.active_account]["selected"] = value
    @property
    def character_requests(self):
        return self.account_configs[self.active_account]["character_requests"]
    @character_requests.setter
    def character_requests(self, value):
        self.account_configs[self.active_account]["character_requests"] = value
    @property
    def dojo_score_settings(self):
        return self.account_configs[self.active_account]["dojo_score_settings"]
    @dojo_score_settings.setter
    def dojo_score_settings(self, value):
        self.account_configs[self.active_account]["dojo_score_settings"] = value

    def _display_price(self, key, guild_id):
        if key == "dojo_score_detailed": key = "dojo_score"
        return get_point_price(key, guild_id) if self.payment_mode == "points" else get_price(key, guild_id)

    def build_embed(self, guild_id: int):
        labels=[]; total=0
        cfg=self.account_configs[self.active_account]
        labels.append(f"設定先：**{self.active_account}個目 / 作成数 {self.create_count}個**")
        for req in self.character_requests:
            cfg=CHARA_CONFIG[req["service_key"]]
            price=get_special_price(cfg["price_key"], cfg["default"], guild_id)
            extra=f"ID:{','.join(map(str,req['ids']))}"
            if "level" in req: extra += f" / Lv.{req['level']} +{req['plus']}"
            if "form" in req: extra += f" / 形態{req['form']}"
            if "talents" in req: extra += f" / 本能:{req['talents']}"
            labels.append(f"・{req['label']}（{extra}） — {(get_point_price(CHARA_CONFIG[req["service_key"]]["price_key"], guild_id) if self.payment_mode == "points" else price)}{"pt" if self.payment_mode == "points" else "円"}"); total += (get_point_price(CHARA_CONFIG[req["service_key"]]["price_key"], guild_id) if self.payment_mode == "points" else price)
        for key in self.selected:
            parsed=parse_custom_amount_key(key)
            if parsed:
                label=custom_amount_label(*parsed); price=self._display_price(key,guild_id)
            else:
                mapped=VIP_OPTION_MAP.get(key)
                if isinstance(key, str) and key.startswith("legend_detail|"):
                    label="レジェンドマップ詳細指定"; price=self._display_price(key,guild_id)
                elif isinstance(key, str) and key.startswith("ototo_detail|"):
                    label="オトート・城強化詳細指定"; price=self._display_price(key,guild_id)
                elif isinstance(key, str) and key.startswith("lineup_detail|"):
                    label="編成キャラ個別設定"; price=self._display_price(key,guild_id)
                elif isinstance(key, str) and key.startswith("labyrinth_detail|"):
                    label="地底迷宮詳細指定"; price=self._display_price(key,guild_id)
                elif isinstance(key, str) and key.startswith("event_detail|"):
                    label="イベントステージ詳細指定"; price=self._display_price(key,guild_id)
                elif isinstance(key, str) and key.startswith("dojo_score|"):
                    label=f"道場スコア指定（{key.split('|',1)[1]}）"; price=self._display_price(key,guild_id)
                elif isinstance(key, str) and key.startswith("future_score_individual|"):
                    label=future_score_individual_label(key)
                    price=self._display_price(key,guild_id)
                elif isinstance(key, str) and key.startswith("future_score|"):
                    label=future_score_label(key)
                    price=self._display_price(key,guild_id)
                elif key == "dojo_score_detailed":
                    label="道場スコア指定"
                    price=self._display_price("dojo_score",guild_id)
                else:
                    label=next((l for g in NEW_ACCOUNT_GROUPS.values() for l,k in g if k==key), key)
                    price=self._display_price(mapped or key,guild_id) if (mapped in ITEM_CONFIG or isinstance(key,str)) else 0
            labels.append(f"・{label} — {price}{"pt" if self.payment_mode == "points" else "円"}"); total += price
        if self.dojo_score_settings:
            score=self.dojo_score_settings.get("hall_of_initiates")
            # dojo_score_detailed は上で選択表示し、ここでは設定値だけ補足する。
            labels = [x for x in labels if not x.startswith("・道場スコア指定 — ")]
            price=self._display_price("dojo_score",guild_id)
            labels.append(f"・道場スコア指定（{int(score):,}） — {price}{"pt" if self.payment_mode == "points" else "円"}")
            total=sum(self._display_price(k,guild_id) for k in self.selected if k != "dojo_score_detailed") + price + sum(self._display_price(CHARA_CONFIG[r["service_key"]]["price_key"],guild_id) for r in self.character_requests)
        grand_total=0
        for idx in range(1, self.create_count+1):
            item_cfg=self.account_configs[idx]
            subtotal=0
            for item_key in item_cfg["selected"]:
                parsed=parse_custom_amount_key(item_key)
                if parsed:
                    subtotal += self._display_price(item_key, guild_id)
                elif item_key == "dojo_score_detailed":
                    subtotal += self._display_price("dojo_score", guild_id)
                else:
                    subtotal += self._display_price(canonical_price_key(VIP_OPTION_MAP.get(item_key, item_key)), guild_id)
            subtotal += sum(self._display_price(CHARA_CONFIG[r["service_key"]]["price_key"], guild_id) for r in item_cfg["character_requests"])
            grand_total += subtotal
        desc=(f"アカウント種別：**{self.account_label}**\n\n" + ("\n".join(labels) if labels else "・未選択") + f"\n\nこのアカウントの料金：{total}{"pt" if self.payment_mode=="points" else "円"}\n**全{self.create_count}個の合計：{grand_total}{"pt" if self.payment_mode=="points" else "円"}**")
        return discord.Embed(title="🆕 新規垢代行", description=desc, color=0x38bdf8)

class NewAccountExecuteButton(ui.Button):
    def __init__(self):
        # row=4 は NewAccountCustomSelect（幅5）が使用済みのため row=0 に配置する
        super().__init__(label="🛒 購入して新規垢作成", style=discord.ButtonStyle.success, row=4)
    async def callback(self, interaction: discord.Interaction):
        view=self.view
        if not isinstance(view,NewAccountOrderView):
            await interaction.response.send_message("❌ この購入パネルは使用できません。",ephemeral=True); return
        configs=[]
        guild_id=interaction.guild_id or 0
        total=0
        for i in range(1, view.create_count+1):
            cfg=view.account_configs[i]
            keys=list(cfg["selected"])
            char_requests=list(cfg["character_requests"])
            dojo_settings=cfg["dojo_score_settings"]
            subtotal=0
            for k in keys:
                parsed=parse_custom_amount_key(k)
                if parsed: subtotal += get_price(k,guild_id)
                elif k=="dojo_score_detailed": subtotal += get_price("dojo_score",guild_id)
                else: subtotal += get_price(canonical_price_key(VIP_OPTION_MAP.get(k,k)),guild_id)
            subtotal += sum(get_special_price(CHARA_CONFIG[r["service_key"]]["price_key"], CHARA_CONFIG[r["service_key"]]["default"], guild_id) for r in char_requests)
            if getattr(view,"payment_mode","yen")=="points":
                subtotal = sum(get_point_price(k,guild_id) if k != "dojo_score_detailed" else get_point_price("dojo_score",guild_id) for k in keys)
                subtotal += sum(get_point_price(CHARA_CONFIG[r["service_key"]]["price_key"],guild_id) for r in char_requests)
            total += subtotal
            configs.append({"keys":keys,"character_requests":char_requests,"dojo_score_settings":dojo_settings})
        active=configs[view.active_account-1]
        modal=NewAccountPaymentModal(view.account_label, view.account_type, active["keys"], total, active["character_requests"], active["dojo_score_settings"], view, payment_mode=getattr(view,"payment_mode","yen"))
        modal.account_configs=configs
        await interaction.response.send_modal(modal)

class NewAccountPaymentModal(ui.Modal):
    def __init__(self, label: str, account_type: str, keys: list[str], total: int, char_requests=None, dojo_score_settings=None, parent_view=None, payment_mode: str = "yen"):
        super().__init__(title=f"{label} 新規垢注文", timeout=300)
        self.label=label; self.account_type=account_type; self.keys=keys; self.char_requests=char_requests or []; self.dojo_score_settings=dojo_score_settings; self.parent_view=parent_view; self.total=max(0, int(total or 0)); self.payment_mode=payment_mode
        if self.payment_mode == "points":
            self.free_confirm = ui.TextInput(label="ポイント注文確認",placeholder="そのまま送信してください",required=False,max_length=1)
            self.add_item(self.free_confirm)
        elif self.total > 0:
            self.paypay_link = ui.TextInput(label="PayPay 送金リンク", placeholder="https://pay.paypay.ne.jp/xxxx", required=True)
            self.add_item(self.paypay_link)
        else:
            # DiscordのModalはコンポーネント0個では送信できないため、
            # 無料注文ではPayPay欄ではない確認用の任意入力欄を1つだけ置く。
            self.free_confirm = ui.TextInput(
                label="無料注文確認",
                placeholder="そのまま送信してください（入力不要）",
                required=False,
                max_length=1,
            )
            self.add_item(self.free_confirm)
    async def _run_one_account(self, interaction, keys, char_requests, dojo_score_settings):
        try:
            backend_selected = {"s1": [], "s2": [], "s3": [], "s4": []}
            backend_custom = {k: 0 for k in CUSTOM_KEYS}
            backend_legend_stages = {}
            backend_main_story_stages = None
            backend_special_stages = None
            backend_vip_facilities = None
            backend_vip_talent_orbs = None
            backend_ototo_settings = {}
            backend_lineup_settings = None
            backend_event_stage_settings = {}
            backend_event_ticket_items = {}
            backend_labyrinth_characters = None
            backend_future_score_settings = None
            backend_dojo_score_settings = dojo_score_settings if hasattr(self, "dojo_score_settings") else None
            backend_map = {
                "dungeon_medal_99":"labyrinth_medals", "main_clear":"main_story_clear",
                "zombie_clear":"zombie_clear", "makai_clear":"aku_clear", "old_legend_clear":"legend_clear",
                "true_legend_clear":"true_legend_clear", "zero_legend_clear":"zero_legend_clear", "event_clear":"event_clear",
                "gamatoto_max":"gamatoto_max", "gamatoto_legend":"gamatoto_legend", "ototo_max":"ototo_max",
                "shrine_max":"cat_shrine_max", "base_upgrades_max":"base_upgrades_max", "gold_membership":"gold_membership",
                "slots_max":"slots_max", "medals_all":"medal_all", "unlock_enemy_guide":"enemy_book_all",
                "skip_tutorial":"skip_tutorial", "hide_rank_up":"hide_rank_up", "user_rank_rewards_claimed":"user_rank_rewards_claimed",
                "user_rank_rewards_unclaimed":"user_rank_rewards_unclaimed", "catguide_rewards_claimed":"catguide_rewards_claimed",
                "catguide_rewards_unclaimed":"catguide_rewards_unclaimed", "cat_scratcher_reset":"cat_scratcher_reset",
                "add_playtime_720h":"add_playtime_720h", "telop_delete":"telop_delete", "ad_free":"ad_free",
                "unlock_all_cats":"unlock_all_cats", "max_all_cats_plus":"max_all_cats_plus",
                "max_all_cats":"max_all_cats", "true_form_all":"true_form_all", "talents_all":"talents_all",
                "talents_disable_all":"talents_disable_all", "remove_error_cats":"remove_error_cats", "all_missions_clear":"all_missions_clear",
            }
            custom_kind_to_backend = {
                "catfood":"custom_catfood", "xp":"custom_xp", "np":"custom_np", "normal_tickets":"custom_normal_tickets",
                "rare_tickets":"custom_rare_tickets", "platinum_tickets":"custom_platinum_tickets", "legend_tickets":"custom_legend_tickets",
                "leadership":"custom_leadership", "battle_items":"custom_battle_items", "catamins":"custom_catamins",
                "catseyes":"custom_catseyes", "base_materials":"custom_base_materials", "matatabi":"custom_matatabi",
                "talent_orbs":"custom_talent_orbs", "base_upgrades":"custom_base_upgrades", "event_tickets":"custom_event_tickets",
            }
            for key in keys:
                if isinstance(key, str) and (key.startswith("future_score|") or key.startswith("future_score_individual|")):
                    backend_selected["s1"].append(key)
                    continue
                parsed = parse_custom_amount_key(key)
                if parsed:
                    kind, amount = parsed
                    bk = custom_kind_to_backend.get(kind)
                    if bk:
                        backend_custom[bk] = amount
                        backend_selected["s1"].append(bk)
                    continue
                mapped = backend_map.get(key)
                if mapped:
                    backend_selected["s1"].append(mapped)
            character_settings=[]; char_ids=[]
            for req in char_requests:
                char_ids.extend(str(x) for x in req["ids"])
                sk=req["service_key"]
                if sk=="chara_unlock": backend_selected["s3"].append("unlock_specific")
                elif sk=="chara_delete": backend_selected["s3"].append("remove_specific")
                elif sk=="chara_lvmax_plus": backend_selected["s3"].append("max_specific")
                elif sk=="chara_lvmax": backend_selected["s3"].append("max_specific_2")
                elif sk=="chara_form": backend_selected["s3"].append("true_form_specific")
                elif sk=="chara_level_plus": backend_selected["s3"].append("level_specific")
                elif sk=="chara_form_select": backend_selected["s3"].append("form_specific")
                elif sk=="chara_talents": backend_selected["s3"].append("talents_specific")
                for cid in req["ids"]:
                    character_settings.append({"id":int(cid),"form":int(req.get("form",1)),"base_level":int(req.get("level",60)),"plus_level":int(req.get("plus",0)),"level_mode":"individual","talent_action":"set","talents":{}})
            # 未来編スコアの注文キーを新規垢バックエンドへ渡す。
            for raw_key in keys:
                if not isinstance(raw_key,str): continue
                if raw_key.startswith("future_score|"):
                    try:
                        _,pos,score=raw_key.split("|",2); pos=int(pos)
                        if score.startswith("random:"):
                            backend_future_score_settings = backend_future_score_settings or {}
                            backend_future_score_settings[pos]={"individual":json.loads(score[7:])}
                        else:
                            backend_future_score_settings = backend_future_score_settings or {}
                            backend_future_score_settings[pos]=int(score)
                    except Exception: logger.exception("future score parse failed")
                elif raw_key.startswith("future_score_individual|"):
                    try:
                        _,pos,payload=raw_key.split("|",2); backend_future_score_settings=backend_future_score_settings or {}; backend_future_score_settings[int(pos)]={"individual":json.loads(payload)}
                    except Exception: logger.exception("future individual score parse failed")
            # Discord詳細指定キーをWeb版と同じ引数へ変換する。
            for raw_key in keys:
                if not isinstance(raw_key,str) or "|" not in raw_key: continue
                prefix,payload=raw_key.split("|",1)
                try:
                    data=json.loads(payload)
                    if prefix=="legend_detail":
                        for series,maps in data.items(): backend_legend_stages.setdefault(series,{}).update(maps)
                    elif prefix=="main_stage_detail":
                        backend_main_story_stages = data
                    elif prefix=="special_stage_detail":
                        backend_special_stages = data
                    elif prefix=="facility_detail":
                        backend_vip_facilities = data
                    elif prefix=="talent_orb_detail":
                        backend_vip_talent_orbs = data
                    elif prefix=="event_ticket_detail":
                        backend_event_ticket_items = data
                    elif prefix=="dojo_score":
                        backend_dojo_score_settings={"hall_of_initiates":int(payload)}
                    elif prefix=="ototo_detail":
                        backend_ototo_settings.update(data)
                    elif prefix=="lineup_detail":
                        backend_lineup_settings=data
                    elif prefix=="event_detail":
                        for fam,maps in data.items(): backend_event_stage_settings.setdefault(fam,{}).update(maps)
                    elif prefix=="labyrinth_detail":
                        backend_event_stage_settings.setdefault("_labyrinth_characters",data); backend_labyrinth_characters=data
                except Exception:
                    logger.exception("new account advanced key parse failed: %s",raw_key)
            backend_vip_items = {}
            if backend_event_ticket_items:
                backend_vip_items["event_tickets"] = backend_event_ticket_items
            backend_selected={k:list(dict.fromkeys(v)) for k,v in backend_selected.items()}
            job_id=str(uuid.uuid4()); now=time.time()
            _create_job(job_id,{"status":"pending","created_at":now,"updated_at":now,"source":"discord"})
            await asyncio.get_running_loop().run_in_executor(None, functools.partial(
                run_job_create, job_id, backend_selected, char_ids, backend_custom,
                count=1, custom_playtime="", account_type_key=self.account_type,
                main_story_chapters=None, vip_items=backend_vip_items or None,
                legend_stages=backend_legend_stages or None, vip_facilities=backend_vip_facilities,
                vip_talent_orbs=backend_vip_talent_orbs, special_stages=backend_special_stages, character_settings=character_settings,
                main_story_stages=backend_main_story_stages, event_stage_settings=backend_event_stage_settings or None,
                lineup_settings=backend_lineup_settings, ototo_settings=backend_ototo_settings or None,
                dojo_score_settings=backend_dojo_score_settings, future_score_settings=backend_future_score_settings,
                access_tier="discord"
            ))
            result=_load_job(job_id) or {}
            if result.get("status")!="done":
                raise RuntimeError(result.get("error") or "新規アカウント作成に失敗しました。")
            return result
        except Exception:
            logger.exception("single new-account creation failed")
            raise

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        if self.payment_mode == "points":
            gid=interaction.guild_id or 0
            if _point_change(gid,interaction.user.id,-self.total,f"新規垢:{self.label}利用") is None:
                await interaction.followup.send(f"❌ ポイント不足です。必要：{self.total:,}pt / 残高：{_point_get(gid,interaction.user.id):,}pt",ephemeral=True); return
        elif self.total>0 and not await paypay_receive(interaction,self.paypay_link.value,self.total,self.label): return
        order_text=[f"新規垢:{self.label} ×{len(getattr(self, 'account_configs', []) or [1])}"]
        for account_index, config in enumerate(getattr(self, "account_configs", []) or [{"keys":self.keys,"character_requests":self.char_requests}], 1):
            order_text.append(f"{account_index}個目")
            order_text.extend(config.get("keys", []))
            order_text.extend(f"{r['label']}[ID:{','.join(map(str,r['ids']))}]" for r in config.get("character_requests", []))
        log_order(interaction.user.id,str(interaction.user),order_text,self.total,"PAID" if self.total else "FREE")
        # Web版と同じ run_job_create() をDiscordから直接呼び出す。
        try:
            configs = getattr(self, "account_configs", None) or [{"keys": self.keys, "character_requests": self.char_requests, "dojo_score_settings": self.dojo_score_settings}]
            all_accounts = []
            all_applied = []
            for account_index, config in enumerate(configs[:5], 1):
                keys = list(config.get("keys", []))
                char_requests = list(config.get("character_requests", []))
                dojo_score_settings = config.get("dojo_score_settings")
                result = await self._run_one_account(interaction, keys, char_requests, dojo_score_settings)
                accounts = result.get("accounts") or []
                for account in accounts:
                    account["order_index"] = account_index
                    all_accounts.append(account)
                all_applied.extend(result.get("applied") or [])
            accounts = all_accounts
            lines=[]
            for i,a in enumerate(accounts,1):
                lines.append(f"**{i}個目**\n引き継ぎコード: `{a.get('tc')}`\n認証番号: `{a.get('ac')}`")
            applied=list(dict.fromkeys(all_applied))
            embed=discord.Embed(title="🎉 新規アカウント作成完了", description="\n\n".join(lines), color=0x00cc88)
            if applied:
                embed.add_field(name="適用内容", value="\n".join(f"✅ {x}" for x in applied)[:1024], inline=False)
            await interaction.followup.send(embed=embed, ephemeral=True)
            try: await interaction.user.send(embed=embed)
            except discord.Forbidden: pass

            # 注文が正常終了したら、親の新規垢パネルに残っている
            # 「指定個数|数量」の選択値だけをリセットする。
            # これをしないと、次回に指定値を入力しなくても前回の数量が再利用される。
            if self.parent_view is not None:
                self.parent_view.selected = {
                    k for k in self.parent_view.selected
                    if not parse_custom_amount_key(k)
                }
            # 新規垢作成が正常終了した場合も代行実績へ投稿する。
            # アカウント種別は「新規垢: 上級者垢」ではなく、
            # 「上級者垢 x5」のように作成個数をまとめて表示する。
            account_count = len(getattr(self, "account_configs", []) or [1])
            account_label = ACCOUNT_PRESET_LABELS.get(self.account_type, self.label)
            jisseki_items = [f"{account_label} x{account_count}"]

            # セーブへ実際に適用された追加サービスも実績へ残す。
            # ただし旧形式のアカウント種別表記は重複させない。
            for item in applied:
                cleaned = str(item)
                for prefix in ("新規垢: ", "新規垢："):
                    if cleaned.startswith(prefix):
                        cleaned = cleaned[len(prefix):].strip()
                        break
                if cleaned == account_label or cleaned.startswith(account_label + " x"):
                    continue
                if cleaned and cleaned not in jisseki_items:
                    jisseki_items.append(cleaned)
            if self.payment_mode != "points" and self.total > 0:
                _point_change(interaction.guild_id or 0, interaction.user.id, int(self.total)//10, "代行利用10%還元")
            await post_jisseki(
                interaction.client,
                interaction.user,
                jisseki_items,
                self.total,
                interaction.guild_id,
                unit=("pt" if self.payment_mode == "points" else "円"),
            )
        except Exception as e:
            logger.error("Discord new account backend error", exc_info=True)
            if self.payment_mode == "points":
                await _refund_point_charge((interaction.guild_id or 0, interaction.user.id, self.total), "新規垢作成失敗返還")
            await interaction.followup.send(embed=discord.Embed(title="❌ 新規垢作成失敗", description=f"{str(e)[:1000]}", color=0xff3333), ephemeral=True)

class AccountPresetView(ui.View):
    def __init__(self, guild_id: int = 0, payment_mode: str = "yen"):
        super().__init__(timeout=None)
        self.payment_mode = payment_mode
        self.add_item(AccountPresetSelect(guild_id, payment_mode))


class AccountPresetSelect(ui.Select):
    def __init__(self, guild_id: int, payment_mode: str = "yen"):
        self.payment_mode = payment_mode
        options = []
        # 垢パネルは「4種の垢プリセット + 垢サービス3種」の7項目をまとめて表示
        preset_items = [
            ("new", "初期垢"),
            ("beginner", "初心者垢"),
            ("intermediate", "中級者垢"),
            ("advanced", "上級者垢"),
        ]
        for key, label in preset_items:
            total = get_account_preset_price(key, guild_id)
            options.append(discord.SelectOption(
                label=label, value=key, description=(f"{get_point_price("__account_" + key + "__", guild_id):,}pt" if self.payment_mode == "points" else f"{total:,}円")
            ))

        options.extend([
            discord.SelectOption(
                label="垢複製", value="clone",
                description=(f"{get_point_price('__clone__', guild_id):,}pt / セーブをそのままコピー" if self.payment_mode=="points" else f"{get_special_price('__clone__', CLONE_PRICE_DEFAULT, guild_id):,}円 / セーブをそのままコピー")
            ),
            discord.SelectOption(
                label="代行全適応垢", value="full_edit",
                description=(f"{get_point_price('__full_edit__', guild_id):,}pt / 全アイテム適応済み" if self.payment_mode=="points" else f"{get_special_price('__full_edit__', FULL_EDIT_PRICE_DEFAULT, guild_id):,}円 / 全アイテム適応済み")
            ),
            discord.SelectOption(
                label="アカウント復旧", value="recovery",
                description=(f"{get_point_price('__recovery__', guild_id):,}pt / 引き継ぎコードで復旧" if self.payment_mode=="points" else f"{get_special_price('__recovery__', RECOVERY_PRICE_DEFAULT, guild_id):,}円 / 引き継ぎコードで復旧")
            ),
        ])
        super().__init__(
            placeholder="▼ アカウントサービスを選択",
            min_values=1, max_values=1, options=options,
            custom_id="account_preset_select", row=0,
        )

    async def callback(self, interaction: discord.Interaction):
        key = self.values[0]

        if key in {"new", "beginner", "intermediate", "advanced"}:
            labels = {
                "new": "初期垢", "beginner": "初心者垢",
                "intermediate": "中級者垢", "advanced": "上級者垢",
            }
            label = labels[key]
            keys = []
            total = get_account_preset_price(key, interaction.guild_id or 0)
            gid = interaction.guild_id or 0
            preset_view = NewAccountOrderView(gid, key, label, payment_mode=self.payment_mode)
            preset_view.selected.update(keys)
            await interaction.response.send_message(
                embed=preset_view.build_embed(gid),
                view=preset_view,
                ephemeral=True,
            )
            return

        special = {
            "clone": (
                "垢複製", "__clone__", CLONE_PRICE_DEFAULT,
                "セーブデータをそのままコピーして新しい引き継ぎコードを発行します。\n※ 元の垢のコードはそのまま有効です。",
                [], True, True,
            ),
            "full_edit": (
                "代行全適応垢", "__full_edit__", FULL_EDIT_PRICE_DEFAULT,
                "全アイテムを適応した垢を作成します。",
                list(ITEM_CONFIG.keys()), False, False,
            ),
            "recovery": (
                "アカウント復旧", "__recovery__", RECOVERY_PRICE_DEFAULT,
                "引き継ぎコードからアカウントを復旧して新しいコードを発行します。",
                [], True, False,
            ),
        }
        label, price_key, default_price, desc, keys, no_edit, is_clone = special[key]
        price = get_special_price(price_key, default_price, interaction.guild_id)
        embed = discord.Embed(title=f"👤 {label}", color=0x5865F2)
        embed.add_field(name="内容", value=desc, inline=False)
        embed.add_field(name="料金", value=(f"{get_point_price(price_key, interaction.guild_id or 0):,}pt" if self.payment_mode == "points" else f"{price:,}円"), inline=False)
        view = ui.View(timeout=300)

        class ConfirmBtn(ui.Button):
            def __init__(self):
                super().__init__(label="🛒購入する", style=discord.ButtonStyle.success)

            async def callback(self, bi: discord.Interaction):
                await bi.response.send_modal(PointServiceModal(label, get_point_price(price_key, bi.guild_id or 0), keys, no_edit=no_edit) if self.payment_mode == "points" else ServiceModal(label, price, keys, no_edit=no_edit))

        view.add_item(ConfirmBtn())
        await interaction.response.send_message(embed=embed, view=view, ephemeral=True)


class AccountPresetConfirmView(ui.View):
    def __init__(self, label: str, keys: list[str], total: int):
        super().__init__(timeout=300)
        self.label = label
        self.keys = keys
        self.total = max(0, int(total or 0))

    @ui.button(label="購入して実行", style=discord.ButtonStyle.success)
    async def confirm(self, interaction: discord.Interaction, button: ui.Button):
        await interaction.response.send_modal(
            AccountInputModal(self.label, self.keys, self.total)
        )


class AccountInputModal(ui.Modal):
    def __init__(self, label: str, keys: list[str], total: int):
        super().__init__(title=f"{label} 情報入力", timeout=300)
        self.label = label
        self.keys = keys
        self.total = max(0, int(total or 0))
        self.t_code = ui.TextInput(
            label="引き継ぎコード",
            placeholder="1a2b3c4d5",
            max_length=9,
            required=(bool(keys)),
        )
        self.a_code = ui.TextInput(
            label="認証番号",
            placeholder="1234",
            max_length=4,
            required=(bool(keys)),
        )
        if self.total > 0:
            self.paypay_link = ui.TextInput(
                label="PayPay送金リンク",
                placeholder="https://pay.paypay.ne.jp/xxxx",
                required=True,
            )
            self.add_item(self.paypay_link)
        self.add_item(self.t_code)
        self.add_item(self.a_code)

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        if self.total > 0:
            if not await paypay_receive(interaction, self.paypay_link.value, self.total, self.label):
                return
        log_order(
            interaction.user.id, str(interaction.user),
            [self.label], self.total, "PAID" if self.total else "FREE"
        )
        if not self.keys:
            await interaction.followup.send(
                embed=discord.Embed(
                    title=f"✅ {self.label}",
                    description="初期垢プリセットは編集なしです。新規アカウント生成は現行bcsfeバックエンドに未搭載のため、セーブ編集なしで終了しました。",
                    color=0x00cc88,
                ),
                ephemeral=True,
            )
            return
        await bcsfe_process(
            interaction,
            self.t_code.value,
            self.a_code.value,
            self.keys,
            [self.label],
            self.total,
        )


async def set_jisseki_channel_cmd(interaction: discord.Interaction):
    if not is_admin(interaction.user.id):
        await interaction.response.send_message("管理者のみ使用できます。", ephemeral=True)
        return

    settings = load_settings(interaction.guild_id)
    settings["jisseki_channel_id"] = str(interaction.channel_id)
    save_settings(interaction.guild_id, settings)

    await interaction.response.send_message(
        f"✅ このチャンネル ({interaction.channel.mention}) を代行実績チャンネルに設定しました。\n"
        "代行処理が成功するたびに、依頼者・利用金額・代行内容をここへ自動投稿します。",
        ephemeral=True,
    )


async def grant_sub_admin_cmd(interaction: discord.Interaction, user_id: str):
    # このコマンドを使えるのは本物のADMIN_IDSのみ。サブ管理者は付与できない。
    if not is_admin(interaction.user.id):
        await interaction.response.send_message("❌ このコマンドはADMIN_IDSの管理者のみ使用できます。", ephemeral=True)
        return

    raw = str(user_id).strip().replace("<@", "").replace(">", "").replace("!", "")
    if not raw.isdigit():
        await interaction.response.send_message("❌ DiscordのユーザーIDを数字で入力してください。", ephemeral=True)
        return

    target_id = int(raw)
    if target_id in ADMIN_IDS:
        await interaction.response.send_message("⚠️ そのユーザーは既にADMIN_IDSの本管理者です。", ephemeral=True)
        return
    if target_id in SUB_ADMIN_IDS:
        await interaction.response.send_message(f"ℹ️ <@{target_id}> は既にサブ管理者です。", ephemeral=True)
        return

    SUB_ADMIN_IDS.append(target_id)
    SUB_ADMIN_IDS[:] = list(dict.fromkeys(SUB_ADMIN_IDS))
    _save_sub_admin_ids()
    await interaction.response.send_message(
        f"✅ <@{target_id}> にサブ管理者権限を付与しました。\n"
        "・値段変更：使用可能\n"
        "・にゃんこパネル設置：使用可能\n"
        "・管理者権限付与：使用不可",
        ephemeral=True,
    )


async def revoke_sub_admin_cmd(interaction: discord.Interaction, user_id: str):
    # このコマンドを使えるのは本物のADMIN_IDSのみ。サブ管理者は削除できない。
    if not is_admin(interaction.user.id):
        await interaction.response.send_message("❌ このコマンドはADMIN_IDSの管理者のみ使用できます。", ephemeral=True)
        return

    raw = str(user_id).strip().replace("<@", "").replace(">", "").replace("!", "")
    if not raw.isdigit():
        await interaction.response.send_message("❌ DiscordのユーザーIDを数字で入力してください。", ephemeral=True)
        return

    target_id = int(raw)
    if target_id in ADMIN_IDS:
        await interaction.response.send_message("⚠️ そのユーザーはADMIN_IDSの本管理者なので削除できません。", ephemeral=True)
        return
    if target_id not in SUB_ADMIN_IDS:
        await interaction.response.send_message(f"ℹ️ <@{target_id}> はサブ管理者ではありません。", ephemeral=True)
        return

    SUB_ADMIN_IDS[:] = [uid for uid in SUB_ADMIN_IDS if int(uid) != target_id]
    _save_sub_admin_ids()
    await interaction.response.send_message(
        f"✅ <@{target_id}> のサブ管理者権限を削除しました。\n"
        "・値段変更：使用不可\n"
        "・にゃんこパネル設置：使用不可\n"
        "・管理者権限付与：使用不可",
        ephemeral=True,
    )


async def point_auth_cmd(interaction: discord.Interaction):
    if not POINT_UDID_WEB_URL:
        await interaction.response.send_message('❌ POINT_UDID_WEB_URL が未設定です。管理者に設定してもらってください。',ephemeral=True); return
    token=_point_create_auth_token(interaction.guild_id or 0,interaction.user.id)
    if not token:
        await interaction.response.send_message("❌ POINT_UDID_SHARED_SECRET が未設定です。",ephemeral=True); return
    sep='&' if '?' in POINT_UDID_WEB_URL else '?'
    url=f"{POINT_UDID_WEB_URL}{sep}token={urllib.parse.quote(token)}"
    await interaction.response.send_message(f"📱 **端末認証URL**\n{url}\n\nこのURLは15分で期限切れになります。UDID取得対応環境で開いてください。",ephemeral=True)

async def point_balance_cmd(interaction: discord.Interaction):
    gid=interaction.guild_id or 0; bal=_point_get(gid,interaction.user.id); rows=_point_history(gid,interaction.user.id,8)
    hist='\n'.join(f"{'+' if int(r['delta'])>0 else ''}{int(r['delta'])}pt｜{r['reason']}" for r in rows) or '履歴なし'
    await interaction.response.send_message(embed=discord.Embed(title='💰 ポイント',description=f'残高：**{bal:,}pt**\n\n**最近の履歴**\n{hist}',color=0x00cc88),ephemeral=True)

async def point_panel_cmd(interaction: discord.Interaction):
    if not is_point_admin(interaction.user.id):
        await interaction.response.send_message('❌ 管理者のみ使用できます。',ephemeral=True); return
    gid=interaction.guild_id or 0
    embed=discord.Embed(title='💰 にゃんこ大戦争 ポイント代行',description='ポイントで代行を購入できます。\n招待報酬：1人 **+5pt**\n※招待報酬はDiscordアカウント30日以上＋サーバー在籍24時間以上＋端末認証が条件です。',color=0xf5c542)
    msg=await interaction.channel.send(embed=embed,view=VipPanelView(gid,payment_mode='points'))
    register_panel_message(gid,'point',msg)
    await interaction.response.send_message('✅ ポイント代行パネルを設置しました。',ephemeral=True)

async def vip_panel_cmd(interaction: discord.Interaction):
    if not can_manage_prices_and_panels(interaction.user.id):
        await interaction.response.send_message("管理者のみ使用できます。", ephemeral=True)
        return
    gid = interaction.guild_id or 0
    embed = discord.Embed(
        title="にゃんこ大戦争 代行自販機",
        description="以下のセレクトから選択して購入してください。\n価格はセレクトメニュー内に表示されます",
        color=0x00cc88,
    )
    msg = await interaction.channel.send(embed=embed, view=VipPanelView(gid))
    register_panel_message(gid, "vip", msg)
    await interaction.response.send_message("✅ パネルを設置しました。", ephemeral=True)


class ClonePanelView(ui.View):
    def __init__(self, guild_id: int = 0):
        super().__init__(timeout=None)
        self.add_item(CloneSelectMenu(guild_id))


class CloneSelectMenu(ui.Select):
    def __init__(self, guild_id: int = 0):
        options = [
            discord.SelectOption(label="垢複製",      value="clone",    description=f"{get_special_price('__clone__', CLONE_PRICE_DEFAULT, guild_id)}円 / セーブをそのままコピー"),
            discord.SelectOption(label="代行全適応垢", value="full_edit", description=f"{get_special_price('__full_edit__', FULL_EDIT_PRICE_DEFAULT, guild_id)}円 / 全アイテム適応済み"),
            discord.SelectOption(label="アカウント復旧", value="recovery", description=f"{get_special_price('__recovery__', RECOVERY_PRICE_DEFAULT, guild_id)}円 / 引き継ぎコードで復旧"),
        ]
        super().__init__(
            placeholder="▼ サービスを選択",
            min_values=1, max_values=1,
            options=options,
            custom_id="clone_select_menu",
            row=0
        )

    async def callback(self, interaction: discord.Interaction):
        val = self.values[0]
        gid = interaction.guild_id or 0
        await safe_interaction_message_edit(interaction, view=ClonePanelView(gid))

        if val == "clone":
            label = "垢複製"
            price = get_special_price("__clone__", CLONE_PRICE_DEFAULT, interaction.guild_id)
            desc  = "セーブデータをそのままコピーして新しい引き継ぎコードを発行します。\n※ 元の垢のコードはそのまま有効です。"
            no_edit = True
            keys = []
        elif val == "full_edit":
            label = "代行全適応垢"
            price = get_special_price("__full_edit__", FULL_EDIT_PRICE_DEFAULT, interaction.guild_id)
            desc  = "全アイテムを適応した垢を作成します。"
            no_edit = False
            keys = list(ITEM_CONFIG.keys())
        else:
            label = "アカウント復旧"
            price = get_special_price("__recovery__", RECOVERY_PRICE_DEFAULT, interaction.guild_id)
            desc  = "引き継ぎコードからアカウントを復旧して新しいコードを発行します。"
            no_edit = True
            keys = []

        embed = discord.Embed(title=f" {label} 注文確認", color=0x5865F2)
        embed.add_field(name="内容", value=desc, inline=False)
        embed.add_field(name="料金", value=f"{price}円", inline=False)

        cv = ui.View(timeout=300)
        _label, _price, _keys, _no_edit = label, price, keys, no_edit

        class ConfirmBtn(ui.Button):
            def __init__(self_btn):
                lbl = "🛒購入する" if _price > 0 else "🛒購入する"
                style = discord.ButtonStyle.green if _price > 0 else discord.ButtonStyle.blurple
                super().__init__(label=lbl, style=style)
            async def callback(self_btn, bi: discord.Interaction):
                if _price == 0:
                    await bi.response.send_modal(FreeServiceModal(_label, _keys, _no_edit))
                else:
                    await bi.response.send_modal(ServiceModal(_label, _price, _keys, _no_edit))

        cv.add_item(ConfirmBtn())
        await interaction.response.send_message(embed=embed, view=cv, ephemeral=True)


# =====================
# 指定キャラ パネル
# =====================
CHARA_CONFIG = {
    "chara_unlock":      {"label": "指定キャラ解放",           "price_key": "__chara_unlock__",       "default": CHARA_UNLOCK_PRICE_DEFAULT},
    "chara_delete":      {"label": "指定キャラ削除",           "price_key": "__chara_delete__",       "default": CHARA_DELETE_PRICE_DEFAULT},
    "chara_lvmax_plus":  {"label": "指定キャラLv.Max+",         "price_key": "__chara_lvmax_plus__",   "default": CHARA_LVMAX_PLUS_PRICE_DEFAULT},
    "chara_lvmax":       {"label": "指定キャラLv.Max",           "price_key": "__chara_lvmax__",        "default": CHARA_LVMAX_PRICE_DEFAULT},
    "chara_form":        {"label": "指定キャラ最終形態化",       "price_key": "__chara_form__",         "default": CHARA_FORM_PRICE_DEFAULT},
    "chara_level_plus":  {"label": "指定キャラLv／＋値指定",     "price_key": "__chara_level_plus__",   "default": CHARA_LEVEL_PRICE_DEFAULT},
    "chara_form_select": {"label": "指定キャラ形態指定",         "price_key": "__chara_form_select__",  "default": CHARA_FORM_SELECT_PRICE_DEFAULT},
    "chara_talents":     {"label": "指定キャラ本能設定",         "price_key": "__chara_talents__",      "default": CHARA_TALENT_PRICE_DEFAULT},
}


class CharaModal(ui.Modal, title="指定キャラ 情報入力"):
    t_code      = ui.TextInput(label="引き継ぎコード (Transfer Code)", placeholder="例: ABCDEF1234567890", required=True, style=discord.TextStyle.short)
    a_code      = ui.TextInput(label="認証番号 (Confirmation Code)", placeholder="例: 1234", required=True, max_length=10, style=discord.TextStyle.short)
    chara_ids   = ui.TextInput(label="キャラクターID（複数はカンマ区切り）", placeholder="例: 1, 5, 12, 98", required=True, style=discord.TextStyle.short)

    def __init__(self, service_label: str, total: int):
        super().__init__(title=f"{service_label} 情報入力", timeout=300)
        self.service_label = service_label
        self.total = max(0, int(total or 0))
        if self.total > 0:
            self.paypay_link = ui.TextInput(label="PayPay 送金リンク", placeholder="https://pay.paypay.ne.jp/xxxx", required=True)
            self.add_item(self.paypay_link)

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        await interaction.followup.send(embed=discord.Embed(
            title="⏳ 処理中...",
            description="処理中です。" if self.total == 0 else "PayPay送金確認中です。しばらくお待ちください。",
            color=0xffaa00
        ), ephemeral=True)
        if self.total > 0:
            ok = await paypay_receive(interaction, self.paypay_link.value, self.total, self.service_label)
            if not ok:
                return
        log_order(interaction.user.id, str(interaction.user), [f"{self.service_label}[ID:{self.chara_ids.value}]"], self.total, "PAID" if self.total else "FREE")
        await bcsfe_chara_process(interaction, self.t_code.value, self.a_code.value,
                                  self.service_label, self.chara_ids.value, self.total, earn_points=True)


class CharaPanelView(ui.View):
    def __init__(self, guild_id: int = 0, payment_mode: str = "yen"):
        super().__init__(timeout=None)
        self.payment_mode = payment_mode
        self.add_item(CharaSelectMenu(guild_id, payment_mode))
        self.add_item(CharaIdLookupButton())


class CharaSelectMenu(ui.Select):
    def __init__(self, guild_id: int = 0, payment_mode: str = "yen"):
        self.payment_mode = payment_mode
        options = [
            discord.SelectOption(
                label=v["label"],
                value=k,
                description=f"{get_special_price(v['price_key'], v['default'], guild_id)}円"
            )
            for k, v in CHARA_CONFIG.items()
        ]
        super().__init__(
            placeholder="▼ サービスを選択",
            min_values=1, max_values=1,
            options=options,
            custom_id="chara_select_menu",
            row=0
        )

    async def callback(self, interaction: discord.Interaction):
        key = self.values[0]
        cfg = CHARA_CONFIG[key]
        label = cfg["label"]
        gid = interaction.guild_id or 0
        price = get_special_price(cfg["price_key"], cfg["default"], gid)

        await safe_interaction_message_edit(interaction, view=CharaPanelView(gid))

        embed = discord.Embed(title=f"{label} 注文確認", color=0x00cc88)
        embed.add_field(name="料金", value=f"{price}円", inline=False)

        cv = ui.View(timeout=300)
        _label, _price = label, price
        _payment_mode = self.payment_mode

        class ConfirmBtn(ui.Button):
            def __init__(self_btn):
                super().__init__(label="🛒購入する", style=discord.ButtonStyle.green)
            async def callback(self_btn, bi: discord.Interaction):
                if _price == 0:
                    await bi.response.send_modal(FreeCharaModal(_label))
                else:
                    await bi.response.send_modal(PointCharaModal(_label, get_point_price(cfg["price_key"], bi.guild_id or 0)) if _payment_mode == "points" else CharaModal(_label, _price))

        cv.add_item(ConfirmBtn())
        await interaction.response.send_message(embed=embed, view=cv, ephemeral=True)


class CharacterIdSearchModal(ui.Modal):
    def __init__(self, parent_view=None):
        super().__init__(title="🔍 キャラクターID検索", timeout=300)
        self.parent_view = parent_view
        self.query = ui.TextInput(
            label="キャラクター名",
            placeholder="例：ネコ",
            required=True,
            max_length=100,
        )
        self.add_item(self.query)

    async def on_submit(self, interaction: discord.Interaction):
        query = self.query.value.strip()
        if not query:
            await interaction.response.send_message("❌ キャラクター名を入力してください。", ephemeral=True)
            return

        await interaction.response.defer(ephemeral=True)
        try:
            metadata = await asyncio.to_thread(get_character_metadata)
            characters = metadata.get("characters", [])
            q = query.casefold()
            matches = []
            for char in characters:
                names = char.get("names") or []
                matched_names = [
                    str(name).strip()
                    for name in names
                    if str(name).strip() and q in str(name).casefold()
                ]
                if matched_names:
                    display_name = matched_names[0]
                    if len(names) > 1 and display_name == names[0]:
                        display_name = " / ".join(str(x) for x in names[:3] if str(x).strip())
                    matches.append({"id": int(char.get("id", 0)), "name": display_name})
        except Exception as e:
            print(f"[ERROR] character ID search: {e}")
            await interaction.followup.send(
                "❌ キャラクターデータの取得に失敗しました。しばらくしてからもう一度試してください。",
                ephemeral=True,
            )
            return

        if not matches:
            await interaction.followup.send(
                f"🔎 「{query}」に一致するキャラクターは見つかりませんでした。",
                ephemeral=True,
            )
            return

        view = CharacterIdSearchResultView(query, matches)
        await interaction.followup.send(
            embed=view.make_embed(),
            view=view,
            ephemeral=True,
        )


class CharacterIdSearchResultView(ui.View):
    PAGE_SIZE = 20

    def __init__(self, query: str, matches: list[dict]):
        super().__init__(timeout=300)
        self.query = query
        self.matches = matches
        self.page = 0
        self.refresh_buttons()

    @property
    def page_count(self):
        return max(1, (len(self.matches) + self.PAGE_SIZE - 1) // self.PAGE_SIZE)

    def make_embed(self):
        start = self.page * self.PAGE_SIZE
        page_items = self.matches[start:start + self.PAGE_SIZE]
        lines = [f"`{item['id']}`　{item['name']}" for item in page_items]
        embed = discord.Embed(
            title="🔎 キャラクターID検索結果",
            description=f"「{self.query}」を含むキャラクター：**{len(self.matches)}体**\n\n" + "\n".join(lines),
            color=0x5865F2,
        )
        if self.page_count > 1:
            embed.set_footer(text=f"ページ {self.page + 1}/{self.page_count}")
        return embed

    def refresh_buttons(self):
        self.clear_items()
        if self.page_count > 1:
            prev_btn = ui.Button(label="◀ 前へ", style=discord.ButtonStyle.secondary, disabled=self.page <= 0)
            next_btn = ui.Button(label="次へ ▶", style=discord.ButtonStyle.secondary, disabled=self.page >= self.page_count - 1)

            async def prev_callback(interaction: discord.Interaction):
                self.page -= 1
                self.refresh_buttons()
                await interaction.response.edit_message(embed=self.make_embed(), view=self)

            async def next_callback(interaction: discord.Interaction):
                self.page += 1
                self.refresh_buttons()
                await interaction.response.edit_message(embed=self.make_embed(), view=self)

            prev_btn.callback = prev_callback
            next_btn.callback = next_callback
            self.add_item(prev_btn)
            self.add_item(next_btn)


class CharaIdLookupButton(ui.Button):
    def __init__(self):
        super().__init__(
            label="🔍 キャラクターID検索",
            style=discord.ButtonStyle.secondary,
            custom_id="chara_id_lookup_button",
            row=1
        )

    async def callback(self, interaction: discord.Interaction):
        await interaction.response.send_modal(CharacterIdSearchModal(self.view))



# =====================
# UI
# =====================

# メインパネルは内容ベースで明確に2分割する。
# A: リソース・チケット・ステージ系
_ITEMS_A = [
    "main_clear", "zombie_clear", "old_legend_clear", "true_legend_clear",
    "zero_legend_clear", "makai_clear", "event_clear", "labyrinth_medals",
]
# B: キャラ・施設・その他系
_ITEMS_B = [
    "all_char_unlock", "error_char_delete", "all_char_lv_max", "all_char_max_form", "all_honnou_max",
    "telop_delete", "slot_max", "medal_all", "enemy_book_all", "user_rank_all",
    "playtime_max", "gold_pass", "facility_max", "gamatoto_max", "gamatoto_legend",
    "ad_free", "ototo_max", "shrine_max",
]


async def _show_confirm(interaction: discord.Interaction, selected: list):
    total = sum(get_price(v, interaction.guild_id) for v in selected)
    items_text = "\n".join(f"{ITEM_CONFIG[v]['label']}│{get_price(v, interaction.guild_id)}円" for v in selected)
    await safe_interaction_message_edit(interaction, view=PanelView(interaction.guild_id or 0))
    embed = discord.Embed(title="🛒 注文確認", color=0x00cc88)
    embed.add_field(name="選択アイテム", value=items_text, inline=False)
    embed.add_field(name="合計金額", value=f"{total}円", inline=False)
    confirm_view = ui.View(timeout=300)
    class ConfirmBuyButton(ui.Button):
        def __init__(self_btn):
            super().__init__(label="🛒購入する", style=discord.ButtonStyle.green)
        async def callback(self_btn, bi: discord.Interaction):
            if total == 0:
                await bi.response.send_modal(FreeModal(selected))
            else:
                await bi.response.send_modal(PurchaseModal(selected, total))
    confirm_view.add_item(ConfirmBuyButton())
    await interaction.response.send_message(embed=embed, view=confirm_view, ephemeral=True)


class PanelView(ui.View):
    def __init__(self, guild_id: int = 0):
        super().__init__(timeout=None)
        self._guild_id = guild_id
        self.add_item(PanelItemSelectA(guild_id))
        self.add_item(PanelItemSelectB(guild_id))
        self.add_item(VipCustomSelect())


class PanelItemSelectA(ui.Select):
    def __init__(self, guild_id: int = 0):
        options = [
            discord.SelectOption(label=ITEM_CONFIG[k]["label"], value=k, description=f"{get_price(k, guild_id)}円")
            for k in _ITEMS_A
        ]
        super().__init__(
            placeholder="① リソース・チケット・ステージ系",
            min_values=1, max_values=len(options),
            options=options, custom_id="panel_item_select_a", row=0
        )
    async def callback(self, interaction: discord.Interaction):
        gid = interaction.guild_id or 0
        await safe_interaction_message_edit(interaction, view=PanelView(gid))
        await _show_confirm(interaction, self.values)


class PanelItemSelectB(ui.Select):
    def __init__(self, guild_id: int = 0):
        options = [
            discord.SelectOption(label=ITEM_CONFIG[k]["label"], value=k, description=f"{get_price(k, guild_id)}円")
            for k in _ITEMS_B
        ]
        super().__init__(
            placeholder="② キャラ・施設・その他系",
            min_values=1, max_values=len(options),
            options=options, custom_id="panel_item_select_b", row=1
        )
    async def callback(self, interaction: discord.Interaction):
        gid = interaction.guild_id or 0
        await safe_interaction_message_edit(interaction, view=PanelView(gid))
        await _show_confirm(interaction, self.values)


# =====================
# 一括入力モーダル
# =====================

class FreeServiceModal(ui.Modal, title="引き継ぎコード入力（0円）"):
    t_code = ui.TextInput(
        label="引き継ぎコード (Transfer Code)",
        placeholder="例: ABCDEF1234567890",
        required=True,
        style=discord.TextStyle.short,
    )
    a_code = ui.TextInput(
        label="認証番号 (Confirmation Code)",
        placeholder="例: 1234",
        required=True,
        max_length=10,
        style=discord.TextStyle.short,
    )

    def __init__(self, service_label: str, item_keys: list = None, no_edit: bool = False):
        super().__init__(title=f"{service_label} 情報入力（0円）", timeout=300)
        self.service_label = service_label
        self.item_keys = item_keys or []
        self.no_edit = no_edit

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        await interaction.followup.send(
            embed=discord.Embed(title="⏳ 処理中...", description="セーブデータの取得を行っています。\nしばらくお待ちください。", color=0xffaa00),
            ephemeral=True
        )
        log_order(interaction.user.id, str(interaction.user), [self.service_label], 0, "FREE")
        await bcsfe_process(interaction, self.t_code.value, self.a_code.value,
                            self.item_keys, [self.service_label], 0, no_edit=self.no_edit,
                            is_clone=(self.service_label == "垢複製"))


class FreeCharaModal(ui.Modal, title="指定キャラ 情報入力（0円）"):
    t_code = ui.TextInput(
        label="引き継ぎコード (Transfer Code)",
        placeholder="例: ABCDEF1234567890",
        required=True,
        style=discord.TextStyle.short,
    )
    a_code = ui.TextInput(
        label="認証番号 (Confirmation Code)",
        placeholder="例: 1234",
        required=True,
        max_length=10,
        style=discord.TextStyle.short,
    )
    chara_ids = ui.TextInput(
        label="キャラクターID（複数はカンマ区切り）",
        placeholder="例: 1, 5, 12, 98",
        required=True,
        style=discord.TextStyle.short,
    )

    def __init__(self, service_label: str):
        super().__init__(title=f"{service_label} 情報入力（0円）", timeout=300)
        self.service_label = service_label
        self.total = 0

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        await interaction.followup.send(embed=discord.Embed(title="⏳ 処理中...", description="セーブデータの取得を行っています。\nしばらくお待ちください。", color=0xffaa00), ephemeral=True)
        log_order(interaction.user.id, str(interaction.user),
                  [f"{self.service_label}[ID:{self.chara_ids.value}]"], 0, "FREE")
        await bcsfe_chara_process(interaction, self.t_code.value, self.a_code.value,
                                  self.service_label, self.chara_ids.value, 0)


class FreeModal(ui.Modal, title="引き継ぎコード入力（0円）"):
    t_code = ui.TextInput(
        label="引き継ぎコード (Transfer Code)",
        placeholder="例: ABCDEF1234567890",
        required=True,
        style=discord.TextStyle.short,
    )
    a_code = ui.TextInput(
        label="認証番号 (Confirmation Code)",
        placeholder="例: 1234",
        required=True,
        max_length=10,
        style=discord.TextStyle.short,
    )

    def __init__(self, items: list, parent_view=None):
        super().__init__(timeout=300)
        self.items = list(items)
        self.parent_view = parent_view

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        await interaction.followup.send(
            embed=discord.Embed(
                title="⏳ 処理中...",
                description="セーブデータの取得を行っています。\nしばらくお待ちください。",
                color=0xffaa00
            ),
            ephemeral=True
        )
        log_order(interaction.user.id, str(interaction.user), self.items, 0, "FREE")
        loop = asyncio.get_running_loop()
        try:
            _perf_total_started = time.perf_counter()
            _perf_stage_started = time.perf_counter()
            server_handler, err = await loop.run_in_executor(
                None,
                functools.partial(run_bcsfe_download, self.t_code.value, self.a_code.value, "jp")
            )
            logger.info("[PERF][NyankoPanel] download=%.2fs", time.perf_counter() - _perf_stage_started)
            if server_handler is None:
                await interaction.followup.send(
                    embed=discord.Embed(
                        title="❌ ダウンロード失敗",
                        description=(
                            f"{err}\n\n"
                            "**確認事項:**\n"
                            "- 引き継ぎコード・認証番号が正確か\n"
                            "- コードの有効期限が切れていないか"
                        ),
                        color=0xff3333
                    ),
                    ephemeral=True
                )
                log_order(interaction.user.id, str(interaction.user), self.items, 0, f"DL_FAIL:{err}")
                return

            _perf_stage_started = time.perf_counter()
            applied = apply_edits(server_handler.save_file, self.items)
            logger.info("[PERF][NyankoPanel] apply_edits=%.2fs", time.perf_counter() - _perf_stage_started)

            _perf_stage_started = time.perf_counter()
            codes = await loop.run_in_executor(
                None,
                functools.partial(run_bcsfe_upload, server_handler)
            )
            logger.info("[PERF][NyankoPanel] upload=%.2fs total_so_far=%.2fs", time.perf_counter() - _perf_stage_started, time.perf_counter() - _perf_total_started)
            if codes is None:
                await interaction.followup.send(
                    embed=discord.Embed(
                        title="❌ アップロード失敗",
                        description="サーバーへのアップロードに失敗しました。",
                        color=0xff3333
                    ),
                    ephemeral=True
                )
                log_order(interaction.user.id, str(interaction.user), self.items, 0, "UL_FAIL")
                return

            transfer_code, confirmation_code = codes
            items_text = "\n".join(f"✅ {item}" for item in applied) or "なし"

            embed = discord.Embed(
                title="🎉代行完了",
                description="以下の新しい引き継ぎコードでゲームにログインしてください。",
                color=0x00cc88
            )
            embed.add_field(
                name=" 新しい引き継ぎ情報",
                value=(
                    f"引き継ぎコード: `{transfer_code}`\n"
                    f"認証番号: `{confirmation_code}`"
                ),
                inline=False
            )
            await interaction.followup.send(embed=embed, ephemeral=True)
            try:
                await interaction.user.send(embed=embed)
            except discord.Forbidden:
                pass

            log_order(interaction.user.id, str(interaction.user), self.items, 0, "SUCCESS")
            await post_jisseki(interaction.client, interaction.user, applied, 0, interaction.guild_id)
            if self.parent_view is not None:
                self.parent_view.reset_custom_amounts()

        except ImportError:
            await interaction.followup.send("bcsfe がインストールされていません。管理者にお問い合わせください。", ephemeral=True)
        except Exception as e:
            logger.error(f"代行処理エラー: {e}", exc_info=True)
            await interaction.followup.send(
                embed=discord.Embed(
                    title="❌ 予期しないエラー",
                    description=f"管理者にお問い合わせください。\n```{str(e)[:300]}```",
                    color=0xff3333
                ),
                ephemeral=True
            )
            log_order(interaction.user.id, str(interaction.user), self.items, 0, f"ERROR:{e}")


class PurchaseModal(ui.Modal, title="購入情報入力"):
    t_code = ui.TextInput(
        label="引き継ぎコード (Transfer Code)",
        placeholder="例: ABCDEF1234567890",
        required=True,
        style=discord.TextStyle.short,
    )
    a_code = ui.TextInput(
        label="認証番号 (Confirmation Code)",
        placeholder="例: 1234",
        required=True,
        max_length=10,
        style=discord.TextStyle.short,
    )

    def __init__(self, items: list, total: int, parent_view=None):
        super().__init__(timeout=300)
        self.items = list(items)
        self.parent_view = parent_view
        self.total = max(0, int(total or 0))
        if self.total > 0:
            self.paypay_link = ui.TextInput(
                label="PayPay 送金リンク",
                placeholder="https://pay.paypay.ne.jp/xxxx",
                required=True,
                style=discord.TextStyle.short,
            )
            self.add_item(self.paypay_link)

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)

        await interaction.followup.send(
            embed=discord.Embed(
                title="⏳ 処理中...",
                description="PayPay送金の確認とセーブデータの取得を行っています。\nしばらくお待ちください。",
                color=0xffaa00
            ),
            ephemeral=True
        )

        # =====================
        # PayPay 受取処理
        # =====================
        if self.total > 0:
            if not self.paypay_link.value.strip():
                await interaction.followup.send(
                    embed=discord.Embed(
                        title="❌ PayPay送金リンク未入力",
                        description="有料注文ではPayPay送金リンクを入力してください。",
                        color=0xff3333
                    ),
                    ephemeral=True
                )
                return

            if not PAYPAY_AVAILABLE:
                await interaction.followup.send(
                    embed=discord.Embed(
                        title="❌ PayPay未対応",
                        description="PayPay機能が利用できません。",
                        color=0xff3333
                    ),
                    ephemeral=True
                )
                return

            paypay_data = load_paypay_data()
            user_paypay = paypay_data.get(str(ADMIN_IDS[0]))

            if not user_paypay:
                await interaction.followup.send(
                    embed=discord.Embed(
                        title="❌ 管理者PayPay未登録",
                        description="管理者のPayPayアカウントが登録されていません。",
                        color=0xff3333
                    ),
                    ephemeral=True
                )
                log_order(
                    interaction.user.id,
                    str(interaction.user),
                    self.items,
                    self.total,
                    "ADMIN_NO_PAYPAY"
                )
                return

            link_raw = self.paypay_link.value.strip()
            link_code = link_raw

            if "pay.paypay.ne.jp/" in link_code:
                link_code = link_code.split("pay.paypay.ne.jp/")[-1].split("?")[0]

            link_info = await paypayu.check_link(link_code)

            if not link_info:
                await interaction.followup.send(
                    embed=discord.Embed(
                        title="❌ PayPayリンクエラー",
                        description="有効なPayPay送金リンクを入力してください。",
                        color=0xff3333
                    ),
                    ephemeral=True
                )
                return

            try:
                link_amount = int(
                    link_info["payload"]["pendingP2PInfo"]["amount"]
                )
                if link_amount < self.total:
                    await interaction.followup.send(
                        embed=discord.Embed(
                            title="❌ 金額不足",
                            description=(
                                f"必要金額: {self.total:,}円\n"
                                f"送金リンクの金額: {link_amount:,}円"
                            ),
                            color=0xff3333
                        ),
                        ephemeral=True
                    )
                    return
            except (KeyError, TypeError, ValueError):
                pass

            result = await paypayu.link_rev(
                link_code,
                user_paypay["phone"],
                user_paypay["password"],
                user_paypay["uuid"]
            )

            if result == "LOGINERR":
                await interaction.followup.send(
                    embed=discord.Embed(
                        title="❌ PayPayエラー",
                        description="PayPayの処理に失敗しました。",
                        color=0xff3333
                    ),
                    ephemeral=True
                )
                return

            elif result is not True:
                await interaction.followup.send(
                    embed=discord.Embed(
                        title="❌ PayPay受取失敗",
                        description="PayPay送金の受取に失敗しました。",
                        color=0xff3333
                    ),
                    ephemeral=True
                )
                return

            log_order(
                interaction.user.id,
                str(interaction.user),
                self.items,
                self.total,
                "PAID"
            )
        else:
            log_order(
                interaction.user.id,
                str(interaction.user),
                self.items,
                self.total,
                "FREE"
            )
        # =====================
        # bcsfe セーブ編集処理
        # =====================
        loop = asyncio.get_running_loop()
        try:
            _perf_total_started = time.perf_counter()
            _perf_stage_started = time.perf_counter()
            server_handler, err = await loop.run_in_executor(
                None,
                functools.partial(
                    run_bcsfe_download,
                    self.t_code.value,
                    self.a_code.value,
                    "jp"  
                )
            )
            logger.info("[PERF][NyankoPanel] download=%.2fs", time.perf_counter() - _perf_stage_started)
            if server_handler is None:
                await interaction.followup.send(
                    embed=discord.Embed(
                        title="❌ ダウンロード失敗",
                        description=(
                            f"{err}\n\n"
                            "**確認事項:**\n"
                            "- 引き継ぎコード・認証番号が正確か\n"
                            "- コードの有効期限が切れていないか\n\n"
                            "⚠️ **支払いは既に完了しています。管理者にご連絡ください。**"
                        ),
                        color=0xff3333
                    ),
                    ephemeral=True
                )
                log_order(interaction.user.id, str(interaction.user), self.items, 0, f"DL_FAIL:{err}")
                return

            _perf_stage_started = time.perf_counter()
            applied = apply_edits(server_handler.save_file, self.items)
            logger.info("[PERF][NyankoPanel] apply_edits=%.2fs", time.perf_counter() - _perf_stage_started)

            _perf_stage_started = time.perf_counter()
            codes = await loop.run_in_executor(
                None,
                functools.partial(run_bcsfe_upload, server_handler)
            )
            logger.info("[PERF][NyankoPanel] upload=%.2fs total_so_far=%.2fs", time.perf_counter() - _perf_stage_started, time.perf_counter() - _perf_total_started)
            if codes is None:
                await interaction.followup.send(
                    embed=discord.Embed(
                        title="❌ アップロード失敗",
                        description=(
                            "サーバーへのアップロードに失敗しました。\n"
                            "⚠️ **支払いは既に完了しています。管理者にご連絡ください。**"
                        ),
                        color=0xff3333
                    ),
                    ephemeral=True
                )
                log_order(interaction.user.id, str(interaction.user), self.items, 0, "UL_FAIL")
                return

            transfer_code, confirmation_code = codes
            items_text = "\n".join(f"✅ {item}" for item in applied) or "なし"

            embed = discord.Embed(
                title="🎉代行完了",
                description="以下の新しい引き継ぎコードでゲームにログインしてください。",
                color=0x00cc88
            )
            embed.add_field(
                name=" 新しい引き継ぎ情報",
                value=(
                    f"引き継ぎコード: `{transfer_code}`\n"
                    f"認証番号: `{confirmation_code}`"
                ),
                inline=False
            )
            await interaction.followup.send(embed=embed, ephemeral=True)
            try:
                await interaction.user.send(embed=embed)
            except discord.Forbidden:
                pass

            log_order(interaction.user.id, str(interaction.user), self.items, self.total, "SUCCESS")
            if self.total > 0:
                _point_change(interaction.guild_id or 0, interaction.user.id, int(self.total)//10, "代行利用10%還元")
            await post_jisseki(interaction.client, interaction.user, applied, self.total, interaction.guild_id)
            if self.parent_view is not None:
                self.parent_view.reset_custom_amounts()

        except ImportError:
            await interaction.followup.send(
                "bcsfe がインストールされていません。管理者にお問い合わせください。",
                ephemeral=True
            )
        except Exception as e:
            logger.error(f"代行処理エラー: {e}", exc_info=True)
            await interaction.followup.send(
                embed=discord.Embed(
                    title="❌ 予期しないエラー",
                    description=f"管理者にお問い合わせください。\n```{str(e)[:300]}```",
                    color=0xff3333
                ),
                ephemeral=True
            )
            log_order(interaction.user.id, str(interaction.user), self.items, 0, f"ERROR:{e}")


class PointServiceModal(ui.Modal, title='ポイントアカウント注文'):
    t_code=ui.TextInput(label='引き継ぎコード',required=True)
    a_code=ui.TextInput(label='認証番号',required=True,max_length=10)
    def __init__(self,label,total,keys,no_edit=False):
        super().__init__(title=f'{label} ポイント注文',timeout=300); self.label=label; self.total=max(0,int(total)); self.keys=keys; self.no_edit=no_edit
    async def on_submit(self,interaction):
        await interaction.response.defer(ephemeral=True); gid=interaction.guild_id or 0
        if _point_change(gid,interaction.user.id,-self.total,f'{self.label}利用') is None:
            await interaction.followup.send(f'❌ ポイント不足です。必要：{self.total:,}pt / 残高：{_point_get(gid,interaction.user.id):,}pt',ephemeral=True); return
        await interaction.followup.send('⏳ 処理中...',ephemeral=True)
        await bcsfe_process(interaction,self.t_code.value,self.a_code.value,self.keys,[self.label],self.total,no_edit=self.no_edit,is_clone=(self.label=='垢複製'),point_charge=(gid,interaction.user.id,self.total))

class PointPurchaseModal(ui.Modal, title='ポイント注文'):
    t_code=ui.TextInput(label='引き継ぎコード (Transfer Code)',placeholder='例: ABCDEF1234567890',required=True)
    a_code=ui.TextInput(label='認証番号 (Confirmation Code)',placeholder='例: 1234',required=True,max_length=10)
    def __init__(self,items,total,parent_view=None):
        super().__init__(timeout=300); self.items=list(items); self.total=max(0,int(total)); self.parent_view=parent_view
    async def on_submit(self,interaction):
        await interaction.response.defer(ephemeral=True)
        gid=interaction.guild_id or 0; uid=interaction.user.id
        with _POINT_DB_LOCK:
            bal=_point_get(gid,uid)
            if bal<self.total:
                await interaction.followup.send(f'❌ ポイント不足です。必要：**{self.total:,}pt** / 残高：**{bal:,}pt**',ephemeral=True); return
            newbal=_point_change(gid,uid,-self.total,'代行利用')
        if newbal is None:
            await interaction.followup.send('❌ ポイントの処理に失敗しました。',ephemeral=True); return
        await interaction.followup.send(embed=discord.Embed(title='⏳ 処理中...',description=f'{self.total:,}ptを使用しました。セーブデータを処理しています。',color=0xf5c542),ephemeral=True)
        try:
            await bcsfe_process(interaction,self.t_code.value,self.a_code.value,self.items,[ITEM_CONFIG[k]['label'] if k in ITEM_CONFIG else k for k in self.items],self.total,no_edit=False,point_charge=(gid,uid,self.total))
        except Exception:
            _point_change(gid,uid,self.total,'代行失敗返還')
            raise
        if self.parent_view is not None:
            try:self.parent_view.reset_custom_amounts()
            except:pass

class PointCharaModal(ui.Modal):
    t_code=ui.TextInput(label='引き継ぎコード',required=True)
    a_code=ui.TextInput(label='認証番号',required=True,max_length=10)
    def __init__(self,service_label,total):
        super().__init__(title=f'{service_label} ポイント注文',timeout=300); self.service_label=service_label; self.total=max(0,int(total))
    async def on_submit(self,interaction):
        await interaction.response.defer(ephemeral=True); gid=interaction.guild_id or 0
        if _point_change(gid,interaction.user.id,-self.total,'指定キャラ代行利用') is None:
            await interaction.followup.send(f'❌ ポイント不足です。必要：{self.total:,}pt / 残高：{_point_get(gid,interaction.user.id):,}pt',ephemeral=True); return
        await interaction.followup.send('⏳ 処理中...',ephemeral=True)
        await bcsfe_chara_process(interaction,self.t_code.value,self.a_code.value,self.service_label,self.service_label,self.total,point_charge=(gid,interaction.user.id,self.total))

# =====================
# PayPay OTP モーダル
# =====================
class PayPayOTPModal(ui.Modal, title="PayPay OTP認証"):
    otp_input = ui.TextInput(
        label="ワンタイムパスワード (OTP)",
        placeholder="SMSに届いた認証コードを入力",
        min_length=4,
        max_length=6,
        required=True
    )

    def __init__(self, phone: str, password: str, set_uuid: str, otpid: str, otp_pre: str):
        super().__init__(timeout=300)
        self.phone = phone
        self.password = password
        self.set_uuid = set_uuid
        self.otpid = otpid
        self.otp_pre = otp_pre

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        # SMSの「HK-1234」のようなOTPは、ユーザーには数字部分だけ入力してもらう。
        # PayPayから返された otp_pre を使うので、HKなどの文字を固定しない。
        otp_digits = self.otp_input.value.strip()
        if not otp_digits.isdigit() or not 4 <= len(otp_digits) <= 6:
            await interaction.followup.send(
                embed=discord.Embed(
                    title="❌ OTPエラー",
                    description="OTPは数字4〜6桁で入力してください。\n例：SMSが「HK-1234」なら「1234」だけ入力します。",
                    color=0xff3333
                ),
                ephemeral=True
            )
            return

        prefix = str(self.otp_pre or "").strip()
        if prefix.endswith("-"):
            full_otp = f"{prefix}{otp_digits}"
        else:
            full_otp = f"{prefix}-{otp_digits}"

        otp_result = await paypayu.login_otp(self.set_uuid, full_otp, self.otpid, self.otp_pre)
        if otp_result == "OK":
            data = load_paypay_data()
            data[str(interaction.user.id)] = {
                "phone": self.phone,
                "password": self.password,
                "uuid": self.set_uuid
            }
            save_paypay_data(data)
            await interaction.followup.send(
                embed=discord.Embed(
                    title="✅ PayPay登録完了",
                    description="登録が完了しました。パネルのボタンから購入できます。",
                    color=0x00cc88
                ),
                ephemeral=True
            )
            logger.info(f"PayPay登録: {interaction.user}({interaction.user.id})")
        elif otp_result == "ERR":
            await interaction.followup.send(
                embed=discord.Embed(
                    title="❌ OTPエラー",
                    description="認証コードが正しくありません。",
                    color=0xff3333
                ),
                ephemeral=True
            )
        else:
            await interaction.followup.send(
                embed=discord.Embed(
                    title="⚠️ 不明なエラー",
                    description="管理者にお問い合わせください。",
                    color=0xffaa00
                ),
                ephemeral=True
            )


@app_commands.describe(phone="電話番号（例: 09012345678）", password="PayPayパスワード")
async def paypay_login(interaction: discord.Interaction, phone: str, password: str):
    if not PAYPAY_AVAILABLE:
        await interaction.response.send_message("PayPay機能が利用できません。", ephemeral=True)
        return
    await interaction.response.defer(ephemeral=True)
    set_uuid = str(uuid.uuid4())
    result = await paypayu.login(phone, password, set_uuid)
    if result.get("response_type") == "ErrorResponse":
        await interaction.followup.send(
            embed=discord.Embed(
                title="❌ ログインエラー",
                description="電話番号またはパスワードが正しくありません。",
                color=0xff3333
            ),
            ephemeral=True
        )
        return
    try:
        otpid = result["otp_reference_id"]
        otp_pre = result["otp_prefix"]
    except KeyError:
        await interaction.followup.send("予期しないレスポンスです。", ephemeral=True)
        return

    class OTPButton(ui.Button):
        def __init__(self_btn):
            super().__init__(label="OTPを入力する", style=discord.ButtonStyle.green)

        async def callback(self_btn, btn_interaction: discord.Interaction):
            if btn_interaction.user.id != interaction.user.id:
                await btn_interaction.response.send_message("他のユーザーの操作です。", ephemeral=True)
                return
            await btn_interaction.response.send_modal(
                PayPayOTPModal(phone, password, set_uuid, otpid, otp_pre)
            )

    view = ui.View(timeout=300)
    view.add_item(OTPButton())
    await interaction.followup.send(
        embed=discord.Embed(
            title="📱 SMS認証",
            description="SMSに認証コードが送信されました。\nボタンをクリックしてコードを入力してください。",
            color=0xffaa00
        ),
        view=view,
        ephemeral=True
    )


async def paypay_delete(interaction: discord.Interaction):
    data = load_paypay_data()
    uid = str(interaction.user.id)
    if uid not in data:
        await interaction.response.send_message("登録されたPayPay情報がありません。", ephemeral=True)
        return
    del data[uid]
    save_paypay_data(data)
    await interaction.response.send_message("✅ PayPay情報を削除しました。", ephemeral=True)


class PriceChangeModal(ui.Modal):
    def __init__(self, keys, labels, currents, special: bool = False, defaults=None):
        # 複数選択した項目を同じ価格へ一括変更
        if isinstance(keys, str):
            keys = [keys]
        if isinstance(labels, str):
            labels = [labels]
        if not isinstance(currents, list):
            currents = [currents]
        self.keys = list(keys)
        self.labels = list(labels)
        self.currents = list(currents)
        self.special = special
        self.defaults = defaults or []

        if len(self.labels) == 1:
            title = f"価格変更：{self.labels[0]}"
        else:
            title = f"価格一括変更：{len(self.labels)}項目"
        super().__init__(title=title[:45], timeout=300)

        current_text = str(self.currents[0]) if len(set(map(str, self.currents))) == 1 else ""
        self.amount = ui.TextInput(
            label="新しい価格（円）",
            placeholder="選択した項目すべてにこの価格を設定",
            default=current_text,
            required=True,
            max_length=9,
        )
        self.add_item(self.amount)

    async def on_submit(self, interaction: discord.Interaction):
        try:
            price = int(self.amount.value.replace(",", "").strip())
            if price < 0 or price > 999_999_999:
                raise ValueError
        except ValueError:
            await interaction.response.send_message("❌ 0〜999,999,999円の整数で入力してください。", ephemeral=True)
            return

        gid = interaction.guild_id or 0
        overrides = load_price_overrides(gid)
        for key in self.keys:
            overrides[key] = price
        save_price_overrides(gid, overrides)

        for panel_type in ("main", "vip", "new_account", "account", "chara"):
            await refresh_registered_panel(gid, panel_type)

        if len(self.labels) == 1:
            target_text = f"**{self.labels[0]}**"
        else:
            target_text = f"**{len(self.labels)}項目**\n" + "、".join(self.labels[:20])
            if len(self.labels) > 20:
                target_text += f" ほか{len(self.labels) - 20}項目"

        await interaction.response.send_message(
            f"✅ {target_text} を **{price:,}円** に変更しました。\n"
            "既設パネルの価格表示も更新しました。",
            ephemeral=True,
        )


class PriceChangeSelect(ui.Select):
    def __init__(self, guild_id: int, keys: list[str], row: int, placeholder: str):
        options = [
            discord.SelectOption(
                label=ITEM_CONFIG[k]["label"][:100],
                value=k,
                description=f"現在：{get_price(k, guild_id):,}円"
            ) for k in keys
        ]
        super().__init__(
            placeholder=placeholder,
            min_values=1,
            max_values=len(options),
            options=options,
            row=row,
        )

    async def callback(self, interaction: discord.Interaction):
        keys = list(self.values)
        gid = interaction.guild_id or 0
        labels = [ITEM_CONFIG[k]["label"] for k in keys]
        currents = [get_price(k, gid) for k in keys]
        await interaction.response.send_modal(
            PriceChangeModal(keys, labels, currents)
        )


class PriceChangeSpecialSelect(ui.Select):
    def __init__(self, guild_id: int):
        options = [
            discord.SelectOption(
                label=v["label"][:100],
                value=v["price_key"],
                description=f"現在：{get_special_price(v['price_key'], v['default'], guild_id):,}円"
            )
            for v in CHARA_CONFIG.values()
        ]
        options += [
            discord.SelectOption(label="垢複製", value="__clone__", description=f"現在：{get_special_price('__clone__', CLONE_PRICE_DEFAULT, guild_id):,}円"),
            discord.SelectOption(label="代行全適応垢", value="__full_edit__", description=f"現在：{get_special_price('__full_edit__', FULL_EDIT_PRICE_DEFAULT, guild_id):,}円"),
            discord.SelectOption(label="アカウント復旧", value="__recovery__", description=f"現在：{get_special_price('__recovery__', RECOVERY_PRICE_DEFAULT, guild_id):,}円"),
            *[
                discord.SelectOption(
                    label=ACCOUNT_PRESET_LABELS[k],
                    value=f"__account_{k}__",
                    description=f"現在：{get_account_preset_price(k, guild_id):,}円"
                ) for k in ACCOUNT_PRESET_LABELS
            ],
        ]
        options = options[:25]
        super().__init__(
            placeholder="▼ 指定キャラ・特殊サービスの価格（複数選択可）",
            min_values=1,
            max_values=len(options),
            options=options,
            row=2,
        )

    async def callback(self, interaction: discord.Interaction):
        keys = list(self.values)
        labels_map = {v["price_key"]: v["label"] for v in CHARA_CONFIG.values()}
        labels_map.update({
            "__clone__": "垢複製",
            "__full_edit__": "代行全適応垢",
            "__recovery__": "アカウント復旧",
        })
        labels_map.update({f"__account_{k}__": v for k, v in ACCOUNT_PRESET_LABELS.items()})
        defaults_map = {v["price_key"]: v["default"] for v in CHARA_CONFIG.values()}
        defaults_map.update({
            "__clone__": CLONE_PRICE_DEFAULT,
            "__full_edit__": FULL_EDIT_PRICE_DEFAULT,
            "__recovery__": RECOVERY_PRICE_DEFAULT,
        })
        defaults_map.update({f"__account_{k}__": ACCOUNT_PRESET_PRICE_DEFAULTS[k] for k in ACCOUNT_PRESET_LABELS})

        gid = interaction.guild_id or 0
        labels = [labels_map.get(k, k) for k in keys]
        currents = [get_special_price(k, defaults_map.get(k, 0), gid) for k in keys]
        defaults = [defaults_map.get(k, 0) for k in keys]
        await interaction.response.send_modal(
            PriceChangeModal(keys, labels, currents, special=True, defaults=defaults)
        )


class PriceChangeCustomAmountSelect(ui.Select):
    def __init__(self, guild_id:int):
        options=[discord.SelectOption(label=label,value=f"custom_amount_{kind}",description=f"現在：{get_special_price(f'custom_amount_{kind}',CUSTOM_AMOUNT_PRICES.get(kind, 50),guild_id):,}円") for label,kind in VIP_CUSTOM_OPTIONS]
        super().__init__(placeholder="▼ 指定個数",min_values=1,max_values=len(options),options=options,row=4)
    async def callback(self,interaction):
        keys=[v.removeprefix("custom_amount_") for v in self.values]
        gid=interaction.guild_id or 0
        labels=[dict((k,l) for l,k in VIP_CUSTOM_OPTIONS)[k] for k in keys]
        price_keys=[f"custom_amount_{k}" for k in keys]
        currents=[get_special_price(k, CUSTOM_AMOUNT_PRICES.get(kind,0), gid) for k,kind in zip(price_keys,keys)]
        await interaction.response.send_modal(PriceChangeModal(price_keys,labels,currents,special=True))

class PriceChangeAdvancedSelect(ui.Select):
    def __init__(self,guild_id:int):
        keys=["future_score","dojo_score","legend_detail","event_detail","main_stage_detail","special_stage_detail","ototo_detail","lineup_custom","labyrinth_detail","facility_detail","talent_orb_detail","event_ticket_detail"]
        labels=[ITEM_CONFIG[k]["label"] for k in keys]
        opts=[discord.SelectOption(label=ITEM_CONFIG[k]["label"],value=k,description=f"現在：{get_price(k,guild_id):,}円") for k in keys]
        super().__init__(placeholder="▼ 詳細サービス（未来編・道場・レジェンド等）",min_values=1,max_values=len(opts),options=opts,row=3)
    async def callback(self,interaction):
        keys=list(self.values); gid=interaction.guild_id or 0
        await interaction.response.send_modal(PriceChangeModal(keys,[ITEM_CONFIG[k]["label"] for k in keys],[get_price(k,gid) for k in keys]))

class PriceChangeView(ui.View):
    def __init__(self, guild_id: int):
        super().__init__(timeout=300)
        keys = list(ITEM_CONFIG.keys())
        self.add_item(PriceChangeSelect(guild_id, keys[:25], 0, "▼ 通常サービス 1〜25（複数選択可）"))
        if len(keys) > 25:
            self.add_item(PriceChangeSelect(guild_id, keys[25:50], 1, "▼ 通常サービス 26〜50（複数選択可）"))
        self.add_item(PriceChangeSpecialSelect(guild_id))
        self.add_item(PriceChangeAdvancedSelect(guild_id))
        self.add_item(PriceChangeCustomAmountSelect(guild_id))


def _point_price_keys():
    keys=list(ITEM_CONFIG.keys())
    keys += ["__clone__","__full_edit__","__recovery__"]
    keys += [f"__account_{k}__" for k in ACCOUNT_PRESET_PRICE_DEFAULTS]
    keys += [cfg["price_key"] for cfg in CHARA_CONFIG.values()]
    keys += [f"custom_amount_{k}" for k in CUSTOM_AMOUNT_PRICES]
    return list(dict.fromkeys(keys))

def _point_label_for_key(key):
    if key in ITEM_CONFIG: return ITEM_CONFIG[key]["label"]
    if key == "__clone__": return "垢複製"
    if key == "__full_edit__": return "代行全適応垢"
    if key == "__recovery__": return "アカウント復旧"
    if key.startswith("__account_"): return ACCOUNT_PRESET_LABELS.get(key[len("__account_"):-2], key)
    for cfg in CHARA_CONFIG.values():
        if cfg.get("price_key")==key: return cfg.get("label",key)
    if key.startswith("custom_amount_"): return "指定個数："+key[len("custom_amount_"):]
    return key

class PointPriceChangeSelect(ui.Select):
    def __init__(self,guild_id:int,keys,row:int=0):
        opts=[]
        for k in keys:
            label=_point_label_for_key(k)
            opts.append(discord.SelectOption(label=label[:100],value=k,description=f"現在：{get_point_price(k,guild_id):,}pt"))
        super().__init__(placeholder="▼ ポイント価格を選択",min_values=1,max_values=min(25,len(opts)),options=opts,row=row)
    async def callback(self,interaction):
        if not is_point_admin(interaction.user.id):
            await interaction.response.send_message('❌ 管理者のみ使用できます。',ephemeral=True); return
        gid=interaction.guild_id or 0
        await interaction.response.send_modal(PointPriceChangeModal(list(self.values),gid))

class PointPriceChangeModal(ui.Modal,title='ポイント変更'):
    values_input=ui.TextInput(label='必要ポイント（サービスごとにカンマ区切り）',placeholder='例: 10,30,50',required=True,max_length=500)
    def __init__(self,keys,guild_id):
        super().__init__(timeout=300); self.keys=keys; self.guild_id=guild_id
    async def on_submit(self,interaction):
        vals=[x.strip() for x in self.values_input.value.replace('、',',').split(',') if x.strip()]
        if len(vals)!=len(self.keys) or any((not x.isdigit()) or int(x)<0 for x in vals):
            await interaction.response.send_message('❌ 選択したサービス数と同じ数の0以上の整数を入力してください。',ephemeral=True); return
        ov=load_point_price_overrides(self.guild_id)
        for k,v in zip(self.keys,vals): ov[canonical_price_key(k)]=int(v)
        save_point_price_overrides(self.guild_id,ov)
        await refresh_registered_panel(self.guild_id, 'point')
        await interaction.response.send_message('✅ ポイント価格を変更しました。既設のポイント代行パネルにも反映されます。',ephemeral=True)

class PointPriceChangeView(ui.View):
    def __init__(self,guild_id):
        super().__init__(timeout=300)
        keys=_point_price_keys()
        self.add_item(PointPriceChangeSelect(guild_id,keys[:25],0))
        if len(keys)>25: self.add_item(PointPriceChangeSelect(guild_id,keys[25:50],1))
        if len(keys)>50: self.add_item(PointPriceChangeSelect(guild_id,keys[50:75],2))
        if len(keys)>75: self.add_item(PointPriceChangeSelect(guild_id,keys[75:100],3))

async def change_point_price_cmd(interaction: discord.Interaction):
    if not is_point_admin(interaction.user.id):
        await interaction.response.send_message('❌ 管理者のみ使用できます。',ephemeral=True); return
    await interaction.response.send_message(embed=discord.Embed(title='ポイント変更',description='変更したいサービスを選択して必要ポイント数を入力してください。',color=0xffaa00),view=PointPriceChangeView(interaction.guild_id or 0),ephemeral=True)

async def change_price_cmd(interaction: discord.Interaction):
    if not can_manage_prices_and_panels(interaction.user.id):
        await interaction.response.send_message("管理者のみ使用できます。", ephemeral=True)
        return
    await interaction.response.send_message(
        embed=discord.Embed(
            title="値段変更",
            description="セレクトからサービスを選び、新しい価格を入力してください。変更後は既設パネルのセレクト内価格も更新されます。",
            color=0xffaa00,
        ),
        view=PriceChangeView(interaction.guild_id or 0), ephemeral=True,
    )


