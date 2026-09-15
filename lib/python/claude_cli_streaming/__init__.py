import json
import os
import shlex
import subprocess
import sys
import tempfile
from collections.abc import Iterable
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Any, NoReturn

from lib.python.retry import (
    DEFAULT_MAX_ATTEMPTS,
    contains_transient_marker,
    sleep_before_retry,
)


_TOOL_ARG_KEYS = (
    "file_path", "path", "command", "pattern", "url", "query",
)
_MAX_ARG_LEN = 80


_CONTENT_FILTER_MARKER = "blocked by content filtering"

_TRANSIENT_NETWORK_MARKERS = (
    "socket connection was closed",
    "socket hang up",
    "fetch failed",
    "connection reset",
    "econnreset",
    "etimedout",
    "enotfound",
    "529 overloaded",
    "api error: 529",
)

MAX_CONTENT_FILTER_RETRIES = 2

MAX_MISSING_RESULT_RETRIES = 1

MAX_NETWORK_RETRIES = DEFAULT_MAX_ATTEMPTS

COPYRIGHT_REASON = (
    "The IEEE 1800-2023 LRM is copyrighted; paraphrase rather than"
    " quote. Write original comments and commit messages; do not"
    " copy LRM prose verbatim into source files."
)

CONTENT_FILTER_RETRY_PROMPT = (
    "Your previous response was blocked by the API content filter."
    " Please try again. " + COPYRIGHT_REASON + " Be concise."
)

MISSING_RESULT_RETRY_PROMPT = (
    "The previous step's output stream ended without a final result"
    " event. If the step is complete, reply with a brief confirmation;"
    " otherwise finish the remaining work and then reply."
)


class ContentFilterError(Exception):
    pass


class TransientNetworkError(Exception):
    def __init__(self, stderr: str) -> None:
        self.stderr = stderr
        super().__init__("transient network failure")


class MissingResultEventError(Exception):
    def __init__(
        self, *, session_id: str | None, last_event: str, stderr: str,
    ) -> None:
        self.session_id = session_id
        self.last_event = last_event
        self.stderr = stderr
        sid = session_id or "unknown"
        super().__init__(
            f"session_id={sid}, last_event={last_event}",
        )


class RateLimitError(Exception):
    def __init__(
        self, *,
        rate_limit_info: dict[str, Any] | None,
        synthetic_text: str | None,
        stderr: str,
    ) -> None:
        info = rate_limit_info or {}
        self.rate_limit_type: str | None = info.get("rateLimitType")
        self.resets_at: int | None = info.get("resetsAt")
        self.overage_status: str | None = info.get("overageStatus")
        self.overage_disabled_reason: str | None = (
            info.get("overageDisabledReason")
        )
        self.synthetic_text = synthetic_text
        self.stderr = stderr
        super().__init__(
            f"rate_limit_type={self.rate_limit_type or 'unknown'},"
            f" resets_at={self.resets_at}",
        )


def build_env() -> dict[str, str]:
    env = os.environ.copy()
    env.pop("CLAUDECODE", None)
    env["CLAUDE_CODE_DISABLE_AUTO_MEMORY"] = "1"
    return env


def _truncate(text: str) -> str:
    stripped = text.strip()
    if not stripped:
        return ""
    first = stripped.splitlines()[0]
    if len(first) > _MAX_ARG_LEN:
        return first[: _MAX_ARG_LEN - 3] + "..."
    return first


def format_tool_call(block: dict[str, Any]) -> str:
    name = block.get("name", "?")
    inp = block.get("input") or {}
    for key in _TOOL_ARG_KEYS:
        if key in inp:
            value = str(inp[key])
            if len(value) > _MAX_ARG_LEN:
                value = value[: _MAX_ARG_LEN - 3] + "..."
            return f"  · {name}({value})"
    return f"  · {name}()"


def format_tool_result(block: dict[str, Any]) -> str:
    content = block.get("content")
    if isinstance(content, str):
        text = content
    elif isinstance(content, list):
        parts = [
            c.get("text", "") for c in content
            if isinstance(c, dict) and c.get("type") == "text"
        ]
        text = "".join(parts)
    else:
        text = ""
    summary = _truncate(text)
    return f"  ↳ {summary}" if summary else "  ↳ (empty)"


def extract_session_id(event: dict[str, Any]) -> str | None:
    if event.get("type") != "system":
        return None
    sid = event.get("session_id")
    return sid if isinstance(sid, str) else None


def extract_tool_name(event: dict[str, Any]) -> str | None:
    if event.get("type") != "assistant":
        return None
    blocks = (event.get("message") or {}).get("content") or []
    for block in reversed(blocks):
        if block.get("type") == "tool_use":
            name = block.get("name")
            return name if isinstance(name, str) else None
    return None


def describe_assistant_blocks(event: dict[str, Any]) -> str:
    blocks = (event.get("message") or {}).get("content") or []
    for block in reversed(blocks):
        btype = block.get("type")
        if btype == "tool_use":
            return f"tool_use:{block.get('name', '?')}"
        if btype == "thinking":
            return "thinking"
        if btype == "text":
            return "text"
    return "(empty)"


def describe_user_blocks(
    event: dict[str, Any], last_tool_name: str | None,
) -> str:
    blocks = (event.get("message") or {}).get("content") or []
    for block in blocks:
        if block.get("type") == "tool_result":
            if last_tool_name:
                return f"tool_result for {last_tool_name}"
            return "tool_result"
    return "user (other)"


def describe_result_event(event: dict[str, Any]) -> str:
    if event.get("is_error"):
        return f"result(is_error):{event.get('subtype') or '?'}"
    return f"result:{event.get('subtype') or 'success'}"


class _StreamDiagnostic:
    def __init__(self) -> None:
        self.session_id: str | None = None
        self.last_event: str = "(no events)"
        self.last_tool_name: str | None = None
        self.rate_limit_info: dict[str, Any] | None = None

    def observe_event(self, event: dict[str, Any]) -> None:
        if self.session_id is None:
            self.session_id = extract_session_id(event)
        self.last_tool_name = (
            extract_tool_name(event) or self.last_tool_name
        )
        self.last_event = describe_event(event, self.last_tool_name)
        info = extract_rate_limit_info(event)
        if info is not None:
            self.rate_limit_info = info

    def to_missing_result_error(self, stderr: str) -> "MissingResultEventError":
        return MissingResultEventError(
            session_id=self.session_id,
            last_event=self.last_event,
            stderr=stderr,
        )

    def to_rate_limit_error(
        self, *, synthetic_text: str | None, stderr: str,
    ) -> "RateLimitError":
        return RateLimitError(
            rate_limit_info=self.rate_limit_info,
            synthetic_text=synthetic_text,
            stderr=stderr,
        )


def describe_event(
    event: dict[str, Any], last_tool_name: str | None,
) -> str:
    etype = event.get("type") or "unknown"
    if etype == "assistant":
        return "assistant " + describe_assistant_blocks(event)
    if etype == "user":
        return describe_user_blocks(event, last_tool_name)
    if etype == "system":
        return f"system:{event.get('subtype') or '?'}"
    if etype == "result":
        return describe_result_event(event)
    return etype


def print_assistant_blocks(message: dict[str, Any]) -> None:
    for block in message.get("content") or []:
        btype = block.get("type")
        if btype == "text":
            text = (block.get("text") or "").strip()
            if text:
                print(text, flush=True)
        elif btype == "tool_use":
            print(format_tool_call(block), flush=True)
        elif btype == "thinking":
            print("  ◊ thinking...", flush=True)


def print_user_blocks(message: dict[str, Any]) -> None:
    for block in message.get("content") or []:
        if block.get("type") == "tool_result":
            print(format_tool_result(block), flush=True)


def print_event(event: dict[str, Any]) -> None:
    etype = event.get("type")
    if etype == "assistant":
        print_assistant_blocks(event.get("message") or {})
    elif etype == "user":
        print_user_blocks(event.get("message") or {})


def extract_result(event: dict[str, Any]) -> str | None:
    if event.get("type") != "result":
        return None
    text = event.get("result")
    if isinstance(text, str) and text:
        return text
    return None


def extract_error_result(event: dict[str, Any]) -> str | None:
    if event.get("type") != "result":
        return None
    if not event.get("is_error"):
        return None
    subtype = event.get("subtype") or "?"
    errors = event.get("errors")
    if isinstance(errors, list):
        body = "; ".join(str(e) for e in errors)
    elif errors is None:
        body = ""
    else:
        body = str(errors)
    if body:
        return f"subtype={subtype}, errors={body}"
    return f"subtype={subtype}"


def is_rate_limit_event_error(event: dict[str, Any]) -> bool:
    return (
        event.get("type") == "assistant"
        and event.get("apiErrorStatus") == 429
        and event.get("error") == "rate_limit"
    )


def extract_rate_limit_info(event: dict[str, Any]) -> dict[str, Any] | None:
    if event.get("type") != "rate_limit_event":
        return None
    info = event.get("rate_limit_info")
    return info if isinstance(info, dict) else None


def extract_synthetic_text(event: dict[str, Any]) -> str | None:
    message = event.get("message")
    if not isinstance(message, dict):
        return None
    blocks = message.get("content")
    if not isinstance(blocks, list):
        return None
    for block in blocks:
        if isinstance(block, dict) and block.get("type") == "text":
            text = block.get("text")
            if isinstance(text, str):
                return text
    return None


def is_rate_limit_result_event(event: dict[str, Any]) -> bool:
    return (
        event.get("type") == "result"
        and bool(event.get("is_error"))
        and event.get("api_error_status") == 429
    )


def format_resets_at(resets_at: int | None, now: datetime) -> str:
    if resets_at is None:
        return "unknown"
    reset_local = datetime.fromtimestamp(resets_at).astimezone()
    clock = reset_local.strftime("%Y-%m-%d %H:%M %Z")
    delta_seconds = max(0, resets_at - int(now.timestamp()))
    hours, remainder = divmod(delta_seconds, 3600)
    minutes = remainder // 60
    if hours:
        delta = f"{hours}h{minutes:02d}m"
    else:
        delta = f"{minutes}m"
    return f"{clock} (in {delta})"


def exit_with_error(message: str, stderr: str) -> NoReturn:
    print(
        f"\nERROR: {message}\n--- stderr ---\n{stderr}",
        file=sys.stderr,
    )
    sys.exit(1)


BUILD_TOOL_DENY_PATTERNS = [
    "cmake", "cmake3", "ccmake", "ctest", "cpack",
    "make", "gmake", "bmake", "ninja", "samu",
    "meson", "bazel", "buck2", "scons", "xcodebuild",
    "ccache", "sccache", "distcc",
    "cc", "c++", "gcc*", "g++*", "clang*", "llvm-*",
    "as", "ld", "ld64", "ar", "ranlib", "libtool", "nm", "strip",
    "python", "python2", "python3*", "perl", "ruby", "node", "deno",
    "bun", "osascript",
    "pytest", "py.test", "tox", "nox",
    "*.sh", "test_*", "*_test", "*_tests", "build*/*", "*/build*/*",
]


def write_deny_hook_settings(deny_patterns: list[str]) -> str:
    hook_script = str(Path(__file__).parent / "deny_bash_hook.py")
    parts = [sys.executable, hook_script, *deny_patterns]
    hook_cmd = " ".join(shlex.quote(p) for p in parts)
    settings = {
        "autoMemoryEnabled": False,
        "hooks": {
            "PreToolUse": [
                {
                    "matcher": "Bash",
                    "hooks": [{"type": "command", "command": hook_cmd}],
                },
            ],
        },
    }
    fd, path = tempfile.mkstemp(suffix=".json", prefix="claude_settings_")
    with os.fdopen(fd, "w") as handle:
        json.dump(settings, handle)
    return path


def build_streaming_cmd(
    *,
    model: str,
    settings_path: str,
    continue_session: bool = False,
    effort: str | None = None,
) -> list[str]:
    cmd = [
        "claude", "-p",
        "--model", model,
        "--verbose",
        "--output-format", "stream-json",
        "--dangerously-skip-permissions",
        "--settings", settings_path,
    ]
    if effort is not None:
        cmd.extend(["--effort", effort])
    if continue_session:
        cmd.append("--continue")
    return cmd


@dataclass
class _StreamOutcome:
    result_text: str | None = None
    error_message: str | None = None
    content_filter_seen: bool = False
    transient_network_seen: bool = False
    rate_limit_seen: bool = False
    rate_limit_synthetic: str | None = None


def _consume_events(
    stdout: Iterable[str], diag: "_StreamDiagnostic",
) -> _StreamOutcome:
    outcome = _StreamOutcome()
    for raw in stdout:
        line = raw.strip()
        if not line:
            continue
        if _CONTENT_FILTER_MARKER in line:
            outcome.content_filter_seen = True
        if contains_transient_marker(line, _TRANSIENT_NETWORK_MARKERS):
            outcome.transient_network_seen = True
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        diag.observe_event(event)
        print_event(event)
        if (
            is_rate_limit_event_error(event)
            or is_rate_limit_result_event(event)
        ):
            if not outcome.rate_limit_seen:
                outcome.rate_limit_synthetic = extract_synthetic_text(event)
                outcome.rate_limit_seen = True
            continue
        err = extract_error_result(event)
        if err is not None:
            if _CONTENT_FILTER_MARKER in err:
                outcome.content_filter_seen = True
            outcome.error_message = err
            continue
        extracted = extract_result(event)
        if extracted is not None:
            outcome.result_text = extracted
    return outcome


def run_claude_streaming(
    cmd: list[str], prompt: str, *, env: dict[str, str],
) -> str:
    with subprocess.Popen(
        cmd,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=env,
        bufsize=1,
    ) as proc:
        assert proc.stdin is not None
        assert proc.stdout is not None
        assert proc.stderr is not None
        proc.stdin.write(prompt)
        proc.stdin.close()
        diag = _StreamDiagnostic()
        outcome = _consume_events(proc.stdout, diag)
        stderr = proc.stderr.read()
        return_code = proc.wait()

    if outcome.rate_limit_seen:
        raise diag.to_rate_limit_error(
            synthetic_text=outcome.rate_limit_synthetic, stderr=stderr,
        )
    if _CONTENT_FILTER_MARKER in stderr or outcome.content_filter_seen:
        raise ContentFilterError(
            stderr or outcome.error_message or "blocked by content filtering",
        )
    transient = outcome.transient_network_seen or contains_transient_marker(
        stderr, _TRANSIENT_NETWORK_MARKERS,
    )
    if return_code != 0 and transient:
        raise TransientNetworkError(stderr or "transient network failure")
    if return_code != 0:
        exit_with_error(
            f"Claude CLI exited with code {return_code}", stderr,
        )
    if outcome.error_message is not None:
        exit_with_error(
            f"Claude CLI emitted an error result event: {outcome.error_message}",
            stderr,
        )
    if outcome.result_text is None:
        raise diag.to_missing_result_error(stderr)
    return outcome.result_text


def run_claude_streaming_with_retry(
    cmd: list[str],
    prompt: str,
    *,
    env: dict[str, str],
    retry_cmd: list[str],
    role: str,
) -> str:
    next_cmd, next_prompt = cmd, prompt
    filter_attempts = 0
    missing_result_attempts = 0
    network_attempts = 0
    while True:
        try:
            return run_claude_streaming(next_cmd, next_prompt, env=env)
        except RateLimitError as exc:
            reset_str = format_resets_at(exc.resets_at, datetime.now())
            overage = (
                f"{exc.overage_status or 'unknown'}"
                f" ({exc.overage_disabled_reason or 'unknown'})"
            )
            quoted = exc.synthetic_text or "(no synthetic text)"
            exit_with_error(
                f"{role} hit rate limit; not retrying.\n"
                f"  type={exc.rate_limit_type or 'unknown'},"
                f" resets at {reset_str}\n"
                f"  overage={overage}\n"
                f'  CLI message: "{quoted}"\n'
                "  Re-run the command after the reset;"
                " closed issues will be skipped.",
                exc.stderr,
            )
        except ContentFilterError as exc:
            filter_attempts += 1
            if filter_attempts > MAX_CONTENT_FILTER_RETRIES:
                print(
                    f"ERROR: {role} blocked by content filter after"
                    f" {MAX_CONTENT_FILTER_RETRIES + 1} attempts:"
                    f" {exc}",
                    file=sys.stderr,
                )
                sys.exit(1)
            print(
                f"WARNING: {role} hit content filter (attempt"
                f" {filter_attempts}); retrying with recovery prompt.",
                file=sys.stderr,
            )
            next_cmd, next_prompt = retry_cmd, CONTENT_FILTER_RETRY_PROMPT
        except MissingResultEventError as exc:
            missing_result_attempts += 1
            sid = exc.session_id or "unknown"
            if missing_result_attempts > MAX_MISSING_RESULT_RETRIES:
                exit_with_error(
                    f"{role} stream ended without a result event after"
                    f" {MAX_MISSING_RESULT_RETRIES + 1} attempts;"
                    f" session_id={sid},"
                    f" last_event={exc.last_event}",
                    exc.stderr,
                )
            print(
                f"WARNING: {role} stream ended without a result event"
                f" (attempt {missing_result_attempts});"
                f" session_id={sid},"
                f" last_event={exc.last_event};"
                " retrying with --continue.",
                file=sys.stderr,
            )
            next_cmd, next_prompt = retry_cmd, MISSING_RESULT_RETRY_PROMPT
        except TransientNetworkError as exc:
            network_attempts += 1
            if network_attempts > MAX_NETWORK_RETRIES:
                exit_with_error(
                    f"{role} hit transient network errors after"
                    f" {MAX_NETWORK_RETRIES + 1} attempts",
                    exc.stderr,
                )
            print(
                f"WARNING: {role} transient network/overload error (attempt"
                f" {network_attempts}); re-running after backoff.",
                file=sys.stderr,
            )
            sleep_before_retry(network_attempts - 1)
