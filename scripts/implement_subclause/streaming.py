"""Live streaming runner for Claude CLI invocations.

Wraps the Claude CLI in ``--output-format stream-json`` mode, decodes
each event as it arrives, prints a human-readable summary to the
terminal, and returns the final ``.result`` text.
"""

import json
import subprocess
import sys
from typing import NoReturn


class ContentFilterError(Exception):
    """Raised when the API blocks output due to content filtering."""


_TOOL_ARG_KEYS = (
    "file_path", "path", "command", "pattern", "url", "query",
)
_MAX_ARG_LEN = 80


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


def print_assistant_blocks(message) -> None:
    """Print text and tool_use blocks from an ``assistant`` message."""
    for block in message.get("content") or []:
        btype = block.get("type")
        if btype == "text":
            text = (block.get("text") or "").strip()
            if text:
                print(text, flush=True)
        elif btype == "tool_use":
            print(format_tool_call(block), flush=True)


def print_event(event) -> None:
    """Pretty-print one stream-json event to stdout."""
    if event.get("type") == "assistant":
        print_assistant_blocks(event.get("message") or {})


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
        if "blocked by content filtering" in stderr:
            raise ContentFilterError(stderr)
        exit_with_error(
            f"Claude CLI exited with code {return_code}", stderr,
        )

    if result_text is None:
        exit_with_error("Claude CLI did not emit a result event", stderr)

    return result_text
