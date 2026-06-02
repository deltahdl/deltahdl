"""Live streaming runner for Claude CLI invocations.

Wraps the Claude CLI in ``--output-format stream-json`` mode, decodes
each event as it arrives, and prints assistant text/tool_use/thinking
blocks and user tool_result blocks to the terminal as Claude produces
them. Returns the final ``.result`` text from the terminal ``result``
event so callers can parse structured output after the stream ends.

System, result, and unknown events are consumed silently — only the
substantive content blocks reach the terminal.

Two recoverable failure modes raise typed exceptions so the retry
wrapper can absorb them: ``ContentFilterError`` (output blocked by
the API content filter) and ``MissingResultEventError`` (the CLI
exits 0 without emitting the terminal ``result`` event — a flake we
can recover from with ``--continue``). Other failures (non-zero exit,
non-content-filter error result events) are loud-fatal via
``exit_with_error``.

``build_env`` returns a Claude-safe copy of the current environment
with the ``CLAUDECODE`` flag stripped — required when invoking the
Claude CLI from inside a Claude Code session so the child process
does not inherit the parent's session-mode flag.
"""

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

# Substrings that mark a transient, self-resolving failure: a transport drop
# on the API socket (Node/undici phrasing, distinct from the gh CLI's transport
# errors) or a server-side 529 Overloaded. Both are recoverable by re-running
# the same invocation after backoff. The list lives here rather than in the
# shared retry module. Matched only against a non-zero-exit run, never against
# normative model output (which legitimately discusses "EOF"/"5xx"/"529"), so
# substring matching is safe here.
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

# Re-run the same invocation as-is on a transient socket drop or a 529
# Overloaded. Either can happen before any server-side session exists, so
# --continue has no safe precondition; a fresh re-run does. The full
# DEFAULT_MAX_ATTEMPTS retries give full-jitter backoff that doubles each
# retry, the final one waiting up to a 2**9-second window — long enough to
# ride out a server-side overload before giving up.
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
    """Raised when the Claude CLI output is blocked by content filtering."""


class TransientNetworkError(Exception):
    """Raised when the CLI exits non-zero on a transient socket/network drop.

    Recoverable: the retry wrapper re-runs the same invocation after
    full-jitter backoff. Carries the CLI's ``stderr`` for the eventual
    loud-fatal message once the attempt budget is exhausted.
    """

    def __init__(self, stderr: str) -> None:
        self.stderr = stderr
        super().__init__("transient network failure")


class MissingResultEventError(Exception):
    """Raised when the Claude CLI exits 0 without a terminal result event.

    Carries enough state for the retry wrapper to (a) decide whether to
    retry, (b) print a useful warning, and (c) surface a rich diagnostic
    when the retry budget is exhausted.

    ``session_id`` is the CLI-assigned id from the first ``system``
    event, or ``None`` when the stream ended before that event arrived.
    ``last_event`` is a short description of the last decoded event so
    post-mortems can tell whether the failure pattern is consistent
    (e.g. always after a tool_result). ``stderr`` is the CLI's stderr
    body, captured for the eventual loud-fatal message.
    """

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
    """Raised when the Claude CLI surfaces a rate-limit 429.

    Non-recoverable from inside the streaming runner — the cap resets
    on the API's clock, not ours, so retrying in-process would just
    consume the retry budget against an unchanged failure mode. The
    wrapper translates this into a loud-fatal that names the rate-limit
    type, the reset time in the local zone, and the org's overage
    posture so the operator knows when to re-run.

    The structured ``rate_limit_info`` payload (originally emitted by
    the CLI's ``rate_limit_event``) is unpacked into named attributes
    so callers can read individual fields without re-walking the dict;
    missing sub-keys flatten to ``None``.
    """

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
    """Return a Claude-safe copy of the current environment.

    Strips ``CLAUDECODE`` so a Claude CLI subprocess launched from
    inside a Claude Code session does not inherit the parent's
    session-mode flag.
    """
    env = os.environ.copy()
    env.pop("CLAUDECODE", None)
    return env


def _truncate(text: str) -> str:
    """Return *text*'s first non-empty line, capped at ``_MAX_ARG_LEN``."""
    stripped = text.strip()
    if not stripped:
        return ""
    first = stripped.splitlines()[0]
    if len(first) > _MAX_ARG_LEN:
        return first[: _MAX_ARG_LEN - 3] + "..."
    return first


def format_tool_call(block: dict[str, Any]) -> str:
    """Return a one-line summary of an assistant ``tool_use`` block."""
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
    """Return a one-line summary of a user ``tool_result`` block."""
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
    """Return the session_id from a system event, else None.

    The first event in a stream-json run is normally
    ``{"type":"system", "session_id":"..."}``; capturing the id lets
    a missing-result-event failure be correlated with the CLI's own
    log file under ``~/.claude/projects/...``.
    """
    if event.get("type") != "system":
        return None
    sid = event.get("session_id")
    return sid if isinstance(sid, str) else None


def extract_tool_name(event: dict[str, Any]) -> str | None:
    """Return the most recent tool_use's name in *event*, or None.

    A subsequent ``tool_result`` event does not carry the tool name,
    only an opaque id. Tracking the most recent ``tool_use`` lets the
    diagnostic say e.g. ``tool_result for TodoWrite`` instead of just
    ``tool_result``.
    """
    if event.get("type") != "assistant":
        return None
    blocks = (event.get("message") or {}).get("content") or []
    for block in reversed(blocks):
        if block.get("type") == "tool_use":
            name = block.get("name")
            return name if isinstance(name, str) else None
    return None


def describe_assistant_blocks(event: dict[str, Any]) -> str:
    """Return a short description of the last meaningful assistant block."""
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
    """Return a short description of the user (tool_result) event."""
    blocks = (event.get("message") or {}).get("content") or []
    for block in blocks:
        if block.get("type") == "tool_result":
            if last_tool_name:
                return f"tool_result for {last_tool_name}"
            return "tool_result"
    return "user (other)"


def describe_result_event(event: dict[str, Any]) -> str:
    """Return a short description of a result event."""
    if event.get("is_error"):
        return f"result(is_error):{event.get('subtype') or '?'}"
    return f"result:{event.get('subtype') or 'success'}"


class _StreamDiagnostic:
    """Mutable diagnostic state captured during a streaming run.

    Bundles ``session_id``, ``last_event``, and ``last_tool_name`` into
    one object so ``run_claude_streaming`` stays under pylint's local-
    variable cap. Updated in place by ``observe_event`` as each decoded
    event arrives.
    """

    def __init__(self) -> None:
        self.session_id: str | None = None
        self.last_event: str = "(no events)"
        self.last_tool_name: str | None = None
        self.rate_limit_info: dict[str, Any] | None = None

    def observe_event(self, event: dict[str, Any]) -> None:
        """Update the diagnostic state from a decoded event."""
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
        """Build a MissingResultEventError carrying the captured state."""
        return MissingResultEventError(
            session_id=self.session_id,
            last_event=self.last_event,
            stderr=stderr,
        )

    def to_rate_limit_error(
        self, *, synthetic_text: str | None, stderr: str,
    ) -> "RateLimitError":
        """Build a RateLimitError carrying the captured rate-limit fields.

        ``rate_limit_info`` may be ``None`` when no ``rate_limit_event``
        arrived before the 429 — CLI 2.1.143 emitted the synthetic
        assistant message without a preceding rate_limit_event, so the
        loud-fatal must still surface gracefully when the structured
        payload is unavailable. ``RateLimitError`` flattens ``None`` into
        per-attribute ``None`` defaults.
        """
        return RateLimitError(
            rate_limit_info=self.rate_limit_info,
            synthetic_text=synthetic_text,
            stderr=stderr,
        )


def describe_event(
    event: dict[str, Any], last_tool_name: str | None,
) -> str:
    """Return a one-line description of *event* for diagnostics."""
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
    """Print every block in an ``assistant`` message."""
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
    """Print ``tool_result`` blocks from a ``user`` message."""
    for block in message.get("content") or []:
        if block.get("type") == "tool_result":
            print(format_tool_result(block), flush=True)


def print_event(event: dict[str, Any]) -> None:
    """Print substantive blocks from assistant/user events; ignore the rest."""
    etype = event.get("type")
    if etype == "assistant":
        print_assistant_blocks(event.get("message") or {})
    elif etype == "user":
        print_user_blocks(event.get("message") or {})


def extract_result(event: dict[str, Any]) -> str | None:
    """Return the ``.result`` text from a ``result`` event, else ``None``."""
    if event.get("type") != "result":
        return None
    text = event.get("result")
    if isinstance(text, str) and text:
        return text
    return None


def extract_error_result(event: dict[str, Any]) -> str | None:
    """Return a description for an ``is_error`` result event, else ``None``.

    The Claude CLI emits a valid result event with ``is_error: true`` and
    the error body in ``errors`` (not ``result``) when an upstream error
    occurs (content filter, API error, message-size limit, etc.). The
    extractor surfaces ``subtype`` and ``errors`` so the runner can
    include them in the failure message instead of dropping them.
    """
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
    """Return True when *event* is the synthetic assistant 429.

    Rate-limit 429s surface on a single ``assistant`` event whose
    top-level fields carry ``apiErrorStatus=429`` and ``error="rate_limit"``;
    no terminal ``result`` event follows on this code path, so detecting
    the failure here is the only way to avoid the misleading
    missing-result retry that the wrapper would otherwise enter.
    """
    return (
        event.get("type") == "assistant"
        and event.get("apiErrorStatus") == 429
        and event.get("error") == "rate_limit"
    )


def extract_rate_limit_info(event: dict[str, Any]) -> dict[str, Any] | None:
    """Return the ``rate_limit_info`` dict from a ``rate_limit_event``, else None.

    The CLI emits ``rate_limit_event`` records during the session with
    the org's current cap state (``rateLimitType``, ``resetsAt``,
    ``overageStatus``, ``overageDisabledReason``). Capturing the most
    recent one lets the loud-fatal name a real reset time rather than
    a stand-in placeholder.
    """
    if event.get("type") != "rate_limit_event":
        return None
    info = event.get("rate_limit_info")
    return info if isinstance(info, dict) else None


def extract_synthetic_text(event: dict[str, Any]) -> str | None:
    """Return the first text block in an assistant *event*, else None.

    Quoted verbatim in the loud-fatal so future debuggers see exactly
    what the CLI printed, even when (as on CLI 2.1.143) the text was
    a misleading fabrication.
    """
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
    """Return True when *event* is an error ``result`` event with HTTP 429.

    Belt-and-braces alongside ``is_rate_limit_event_error``: if a future
    CLI version routes the 429 through the ``result`` event path instead
    of synthesising an assistant message, this helper catches it without
    requiring a coordinated runner change.
    """
    return (
        event.get("type") == "result"
        and bool(event.get("is_error"))
        and event.get("api_error_status") == 429
    )


def format_resets_at(resets_at: int | None, now: datetime) -> str:
    """Return a human-readable reset time + delta from *now*.

    Renders ``resets_at`` (unix epoch seconds) in the local timezone with
    a ``(in HhMm)`` delta tail computed against *now*. *now* is injected
    rather than captured from ``datetime.now()`` so the loud-fatal
    timestamp is deterministic in tests and so a caller probing for a
    relative delta can pin both ends. Returns ``"unknown"`` when
    ``resets_at`` is ``None`` (no rate_limit_event arrived before the
    failure).
    """
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
    """Print *message* and *stderr* to stderr and exit with code 1."""
    print(
        f"\nERROR: {message}\n--- stderr ---\n{stderr}",
        file=sys.stderr,
    )
    sys.exit(1)


def write_deny_hook_settings(deny_patterns: list[str]) -> str:
    """Write a temp ``settings.json`` wiring the Bash deny hook.

    The settings install a ``PreToolUse`` hook on ``matcher: "Bash"``
    that invokes ``deny_bash_hook.py`` with *deny_patterns* as
    argv. Hooks fire before the permission layer, so the deny
    survives ``--dangerously-skip-permissions`` (which the CLI is
    still launched with so every other tool auto-approves).

    Returns the absolute path of the temp file; the caller owns its
    lifecycle and must ``os.unlink`` it once the session ends.
    """
    hook_script = str(Path(__file__).parent / "deny_bash_hook.py")
    parts = [sys.executable, hook_script, *deny_patterns]
    hook_cmd = " ".join(shlex.quote(p) for p in parts)
    settings = {
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
    """Return a Claude CLI argv for stream-json mode.

    ``settings_path`` points at a ``settings.json`` (typically the
    file produced by ``write_deny_hook_settings``) so the headless
    session inherits a PreToolUse hook that blocks the blacklisted
    Bash patterns. ``--dangerously-skip-permissions`` stays — every
    other tool auto-approves; the hook is the only thing gating Bash.

    When ``continue_session`` is true, ``--continue`` is appended so
    the call resumes the most recent Claude session rather than
    starting a fresh one — used by multi-step pipelines that keep all
    steps in one session. When *effort* is set, ``--effort {effort}``
    is appended so the Claude CLI applies the named thinking-budget
    tier; left as ``None`` for callers that have not opted into the
    flag.
    """
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
    """Mutable per-event state accumulated by ``_consume_events``.

    Bundled so ``run_claude_streaming`` reads one structured outcome
    instead of juggling five separate locals — keeps the main function
    under pylint's locals-and-branches caps without adding inline
    directives.
    """

    result_text: str | None = None
    error_message: str | None = None
    content_filter_seen: bool = False
    transient_network_seen: bool = False
    rate_limit_seen: bool = False
    rate_limit_synthetic: str | None = None


def _consume_events(
    stdout: Iterable[str], diag: "_StreamDiagnostic",
) -> _StreamOutcome:
    """Decode JSON events from *stdout*, print them, and capture outcome state.

    Rate-limit detection takes precedence over the error-result and
    result-extraction branches — once seen, later events for the same
    failure are skipped without overwriting the first synthetic text.
    The diagnostic is mutated in place so the caller can build either a
    ``MissingResultEventError`` or a ``RateLimitError`` from it after the
    loop returns.
    """
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
    """Run Claude CLI in stream-json mode, printing events live.

    *cmd* must already include ``--output-format stream-json`` and
    ``--verbose``. Returns the final ``.result`` text from the
    terminal ``result`` event.

    Raises ``RateLimitError`` when a rate-limit 429 is detected — the
    cap resets on the API's clock so this is non-recoverable from
    inside the runner; the wrapper translates it into a loud-fatal
    naming the reset time. Raises ``ContentFilterError`` when content
    filtering is detected (in raw stdout, in the errors body of an
    ``is_error`` result event, or in stderr after a non-zero exit) so
    the caller can retry with the recovery prompt. Raises
    ``MissingResultEventError`` when the CLI exits 0 with no terminal
    result event (a CLI-side flake we can recover from with
    ``--continue``); the exception carries the captured ``session_id``
    and a description of the last event seen so the wrapper can warn /
    loud-fatal informatively. Raises ``TransientNetworkError`` when a
    non-zero exit carries a transient socket/network marker (on a streamed
    line or in stderr) so the wrapper can re-run the same invocation after
    backoff. Loud-fatal on every other
    failure (non-zero exit or a non-content-filter error result event).
    """
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
    """Wrap ``run_claude_streaming`` in a recoverable-error retry loop.

    Three recoverable failure modes are absorbed; everything else
    propagates / is loud-fatal in the inner call.

    ``TransientNetworkError``: a transient socket/network drop. Re-runs
    the *same* invocation (``next_cmd``/``next_prompt`` unchanged) after
    full-jitter exponential backoff — a drop can happen before any
    server-side session exists, so ``--continue`` has no safe precondition.
    Up to ``MAX_NETWORK_RETRIES`` retries; loud-fatal afterward.

    ``ContentFilterError``: retry with ``CONTENT_FILTER_RETRY_PROMPT``
    using ``retry_cmd`` (which must include ``--continue`` so it
    resumes the same Claude session). Up to ``MAX_CONTENT_FILTER_RETRIES``
    retries; loud-fatal afterward.

    ``MissingResultEventError``: same retry shape but with
    ``MISSING_RESULT_RETRY_PROMPT``; up to ``MAX_MISSING_RESULT_RETRIES``
    retries. The CLI sometimes exits 0 without emitting the terminal
    ``result`` event after a tool turn — ``--continue`` resumes the
    session and lets the model emit a closing response. The session id
    and last-event diagnostic from the inner exception are surfaced in
    both the warning and (on exhaustion) the loud-fatal message so a
    human can correlate the failure with the CLI's own log file.

    Each error type tracks an independent attempt counter so an
    interleaved failure pattern doesn't double-charge a single budget.
    *role* is the human-readable label ("Step", "Oracle", …) used in
    warning and error messages.

    ``RateLimitError`` is non-recoverable: the cap resets on the API's
    clock, so an in-process retry would just burn the budget against an
    unchanged failure mode. Translates to ``exit_with_error`` with the
    rate-limit type, the local-zone reset time, the org's overage
    posture, the CLI's synthetic text quoted verbatim, and a restart
    hint — the caller's idempotent re-run is the recovery path.
    """
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
