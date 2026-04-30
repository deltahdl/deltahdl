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
"""

import json
import subprocess
import sys
from typing import NoReturn


_TOOL_ARG_KEYS = (
    "file_path", "path", "command", "pattern", "url", "query",
)
_MAX_ARG_LEN = 80


_CONTENT_FILTER_MARKER = "blocked by content filtering"

MAX_CONTENT_FILTER_RETRIES = 2

MAX_MISSING_RESULT_RETRIES = 1

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

    def __init__(self, *, session_id, last_event, stderr) -> None:
        self.session_id = session_id
        self.last_event = last_event
        self.stderr = stderr
        sid = session_id or "unknown"
        super().__init__(
            f"session_id={sid}, last_event={last_event}",
        )


def _truncate(text: str) -> str:
    """Return *text*'s first non-empty line, capped at ``_MAX_ARG_LEN``."""
    stripped = text.strip()
    if not stripped:
        return ""
    first = stripped.splitlines()[0]
    if len(first) > _MAX_ARG_LEN:
        return first[: _MAX_ARG_LEN - 3] + "..."
    return first


def format_tool_call(block) -> str:
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


def format_tool_result(block) -> str:
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


def extract_session_id(event):
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


def extract_tool_name(event):
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
            return block.get("name")
    return None


def describe_assistant_blocks(event) -> str:
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


def describe_user_blocks(event, last_tool_name) -> str:
    """Return a short description of the user (tool_result) event."""
    blocks = (event.get("message") or {}).get("content") or []
    for block in blocks:
        if block.get("type") == "tool_result":
            if last_tool_name:
                return f"tool_result for {last_tool_name}"
            return "tool_result"
    return "user (other)"


def describe_result_event(event) -> str:
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

    def observe_event(self, event) -> None:
        """Update the diagnostic state from a decoded event."""
        if self.session_id is None:
            self.session_id = extract_session_id(event)
        self.last_tool_name = (
            extract_tool_name(event) or self.last_tool_name
        )
        self.last_event = describe_event(event, self.last_tool_name)

    def to_missing_result_error(self, stderr) -> "MissingResultEventError":
        """Build a MissingResultEventError carrying the captured state."""
        return MissingResultEventError(
            session_id=self.session_id,
            last_event=self.last_event,
            stderr=stderr,
        )


def describe_event(event, last_tool_name) -> str:
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


def print_assistant_blocks(message) -> None:
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


def print_user_blocks(message) -> None:
    """Print ``tool_result`` blocks from a ``user`` message."""
    for block in message.get("content") or []:
        if block.get("type") == "tool_result":
            print(format_tool_result(block), flush=True)


def print_event(event) -> None:
    """Print substantive blocks from assistant/user events; ignore the rest."""
    etype = event.get("type")
    if etype == "assistant":
        print_assistant_blocks(event.get("message") or {})
    elif etype == "user":
        print_user_blocks(event.get("message") or {})


def extract_result(event) -> str | None:
    """Return the ``.result`` text from a ``result`` event, else ``None``."""
    if event.get("type") != "result":
        return None
    text = event.get("result")
    if isinstance(text, str) and text:
        return text
    return None


def extract_error_result(event) -> str | None:
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


def exit_with_error(message, stderr) -> NoReturn:
    """Print *message* and *stderr* to stderr and exit with code 1."""
    print(
        f"\nERROR: {message}\n--- stderr ---\n{stderr}",
        file=sys.stderr,
    )
    sys.exit(1)


def build_streaming_cmd(
    *, model: str, disallowed_tools: str, continue_session: bool = False,
) -> list[str]:
    """Return a Claude CLI argv for stream-json mode.

    Both oracles and mutators invoke Claude with the same flag shape
    (only ``--disallowedTools`` differs). Centralise the argv here so
    pylint's duplicate-code rule does not complain about parallel
    blocks in the two caller modules. When ``continue_session`` is
    true, ``--continue`` is appended so the call resumes the most
    recent Claude session rather than starting a fresh one — used by
    the eight-step mutator pipeline to keep all steps in one session.
    """
    cmd = [
        "claude", "-p",
        "--model", model,
        "--verbose",
        "--output-format", "stream-json",
        "--dangerously-skip-permissions",
        "--disallowedTools", disallowed_tools,
    ]
    if continue_session:
        cmd.append("--continue")
    return cmd


def run_claude_streaming(cmd, prompt, *, env) -> str:
    """Run Claude CLI in stream-json mode, printing events live.

    *cmd* must already include ``--output-format stream-json`` and
    ``--verbose``. Returns the final ``.result`` text from the
    terminal ``result`` event.

    Raises ``ContentFilterError`` when content filtering is detected
    (in raw stdout, in the errors body of an ``is_error`` result event,
    or in stderr after a non-zero exit) so the caller can retry with the
    recovery prompt. Raises ``MissingResultEventError`` when the CLI
    exits 0 with no terminal result event (a CLI-side flake we can
    recover from with ``--continue``); the exception carries the
    captured ``session_id`` and a description of the last event seen
    so the wrapper can warn / loud-fatal informatively. Loud-fatal on
    every other failure (non-zero exit or a non-content-filter error
    result event).
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

        result_text: str | None = None
        error_message: str | None = None
        content_filter_seen = False
        diag = _StreamDiagnostic()
        for raw in proc.stdout:
            line = raw.strip()
            if not line:
                continue
            if _CONTENT_FILTER_MARKER in line:
                content_filter_seen = True
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                continue
            diag.observe_event(event)
            print_event(event)
            err = extract_error_result(event)
            if err is not None:
                if _CONTENT_FILTER_MARKER in err:
                    content_filter_seen = True
                error_message = err
                continue
            extracted = extract_result(event)
            if extracted is not None:
                result_text = extracted

        stderr = proc.stderr.read()
        return_code = proc.wait()

    if _CONTENT_FILTER_MARKER in stderr or content_filter_seen:
        raise ContentFilterError(
            stderr or error_message or "blocked by content filtering",
        )

    if return_code != 0:
        exit_with_error(
            f"Claude CLI exited with code {return_code}", stderr,
        )

    if error_message is not None:
        exit_with_error(
            f"Claude CLI emitted an error result event: {error_message}",
            stderr,
        )

    if result_text is None:
        raise diag.to_missing_result_error(stderr)

    return result_text


def run_claude_streaming_with_retry(
    cmd, prompt, *, env, retry_cmd, role: str,
) -> str:
    """Wrap ``run_claude_streaming`` in a recoverable-error retry loop.

    Two recoverable failure modes are absorbed; everything else
    propagates / is loud-fatal in the inner call.

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
    """
    next_cmd, next_prompt = cmd, prompt
    filter_attempts = 0
    missing_result_attempts = 0
    while True:
        try:
            return run_claude_streaming(next_cmd, next_prompt, env=env)
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
