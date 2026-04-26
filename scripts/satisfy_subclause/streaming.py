"""Live streaming runner for Claude CLI invocations.

Wraps the Claude CLI in ``--output-format stream-json`` mode, decodes
each event as it arrives, and prints assistant text/tool_use/thinking
blocks and user tool_result blocks to the terminal as Claude produces
them. Returns the final ``.result`` text from the terminal ``result``
event so callers can parse structured output after the stream ends.

System, result, and unknown events are consumed silently — only the
substantive content blocks reach the terminal.
"""

import json
import subprocess
import sys
from typing import NoReturn


_TOOL_ARG_KEYS = (
    "file_path", "path", "command", "pattern", "url", "query",
)
_MAX_ARG_LEN = 80


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


def exit_with_error(message, stderr) -> NoReturn:
    """Print *message* and *stderr* to stderr and exit with code 1."""
    print(
        f"\nERROR: {message}\n--- stderr ---\n{stderr}",
        file=sys.stderr,
    )
    sys.exit(1)


def build_streaming_cmd(*, model: str, disallowed_tools: str) -> list[str]:
    """Return a Claude CLI argv for stream-json mode.

    Both oracles and mutators invoke Claude with the same flag shape
    (only ``--disallowedTools`` differs). Centralise the argv here so
    pylint's duplicate-code rule does not complain about parallel
    blocks in the two caller modules.
    """
    return [
        "claude", "-p",
        "--model", model,
        "--verbose",
        "--output-format", "stream-json",
        "--dangerously-skip-permissions",
        "--disallowedTools", disallowed_tools,
    ]


def run_claude_streaming(cmd, prompt, *, env) -> str:
    """Run Claude CLI in stream-json mode, printing events live.

    *cmd* must already include ``--output-format stream-json`` and
    ``--verbose``. Returns the final ``.result`` text from the
    terminal ``result`` event. Loud-fatal on non-zero exit or missing
    result.
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
        for raw in proc.stdout:
            line = raw.strip()
            if not line:
                continue
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                continue
            print_event(event)
            extracted = extract_result(event)
            if extracted is not None:
                result_text = extracted

        stderr = proc.stderr.read()
        return_code = proc.wait()

    if return_code != 0:
        exit_with_error(
            f"Claude CLI exited with code {return_code}", stderr,
        )

    if result_text is None:
        exit_with_error("Claude CLI did not emit a result event", stderr)

    return result_text
