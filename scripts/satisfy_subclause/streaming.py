"""Live streaming runner for Claude CLI invocations.

Wraps the Claude CLI in ``--output-format stream-json`` mode, decodes
each event as it arrives, and prints assistant text/tool_use/thinking
blocks and user tool_result blocks to the terminal as Claude produces
them. Returns the final ``.result`` text from the terminal ``result``
event so callers can parse structured output after the stream ends.

System, result, and unknown events are consumed silently — only the
substantive content blocks reach the terminal.

Content-filter errors raise ``ContentFilterError`` so callers can
retry with the recovery prompt; other failures (non-zero exit, missing
result event, non-content-filter error result events) are loud-fatal
via ``exit_with_error``.
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

COPYRIGHT_REASON = (
    "The IEEE 1800-2023 LRM is copyrighted; paraphrase rather than"
    " quote. Write original comments and commit messages; do not"
    " copy LRM prose verbatim into source files."
)

CONTENT_FILTER_RETRY_PROMPT = (
    "Your previous response was blocked by the API content filter."
    " Please try again. " + COPYRIGHT_REASON + " Be concise."
)


class ContentFilterError(Exception):
    """Raised when the Claude CLI output is blocked by content filtering."""


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
    recovery prompt. Loud-fatal on every other failure (non-zero exit,
    missing result event, or a non-content-filter error result event).
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
        exit_with_error("Claude CLI did not emit a result event", stderr)

    return result_text


def run_claude_streaming_with_retry(
    cmd, prompt, *, env, retry_cmd, role: str,
) -> str:
    """Wrap ``run_claude_streaming`` in a content-filter retry loop.

    On ``ContentFilterError`` the retry call uses ``retry_cmd`` (which
    must include ``--continue`` so it resumes the same Claude session)
    and ``CONTENT_FILTER_RETRY_PROMPT``. Up to
    ``MAX_CONTENT_FILTER_RETRIES`` retries; loud-fatal afterward.
    *role* is the human-readable label ("Step", "Oracle", …) used in
    warning and error messages.
    """
    next_cmd, next_prompt = cmd, prompt
    attempt = 0
    while True:
        try:
            return run_claude_streaming(next_cmd, next_prompt, env=env)
        except ContentFilterError as exc:
            attempt += 1
            if attempt > MAX_CONTENT_FILTER_RETRIES:
                print(
                    f"ERROR: {role} blocked by content filter after"
                    f" {MAX_CONTENT_FILTER_RETRIES + 1} attempts:"
                    f" {exc}",
                    file=sys.stderr,
                )
                sys.exit(1)
            print(
                f"WARNING: {role} hit content filter (attempt"
                f" {attempt}); retrying with recovery prompt.",
                file=sys.stderr,
            )
            next_cmd, next_prompt = retry_cmd, CONTENT_FILTER_RETRY_PROMPT
