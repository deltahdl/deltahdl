"""PreToolUse hook script that denies blacklisted Bash commands.

Claude Code's permission layer is bypassed under
``--dangerously-skip-permissions``, which makes the CLI's
``--disallowedTools`` flag a no-op. PreToolUse hooks fire *before*
the permission layer, so they remain authoritative — this script is
the blacklist implementation for the headless sub-Claude sessions
spawned by the satisfaction pipeline.

Wired into a temp ``settings.json`` under
``hooks.PreToolUse[matcher=Bash]``: the hook command is
``python3 /abs/path/to/deny_bash_hook.py <pattern> <pattern> ...``.
Patterns are bare command names (e.g. ``cmake``, ``make``); the
script splits the Bash command on shell operators (``&&``, ``||``,
``;``, ``|``) so a chained invocation like ``cd /tmp && cmake .`` is
still caught.

Exit codes follow the Claude Code hooks contract: 0 = proceed,
2 = block with stderr surfaced to the model as the rejection reason.
Any failure to parse the stdin event (malformed JSON, non-Bash tool,
non-string command) auto-allows — a hook is not the place to enforce
schema invariants the platform already controls.
"""

import json
import re
import shlex
import sys

_SHELL_OPERATOR_RE = re.compile(r"&&|\|\||;|\|")

_TRUNCATE_AT = 80


def _first_token(segment: str) -> str | None:
    """Return the first shlex token of *segment*, or ``None``.

    Empty / whitespace-only segments and segments that shlex cannot
    parse (e.g. unclosed quotes) return ``None`` so callers can
    skip them.
    """
    segment = segment.strip()
    if not segment:
        return None
    try:
        parts = shlex.split(segment)
    except ValueError:
        return None
    return parts[0]


def first_tokens(command: str) -> list[str]:
    """Return the first token of every subcommand inside *command*.

    Splits on ``&&``, ``||``, ``;``, and ``|`` so a chained command
    like ``cd /tmp && cmake .`` yields ``["cd", "cmake"]``. Malformed
    or empty segments are skipped silently.
    """
    tokens: list[str] = []
    for segment in _SHELL_OPERATOR_RE.split(command):
        first = _first_token(segment)
        if first is not None:
            tokens.append(first)
    return tokens


def extract_bash_command(stdin_text: str) -> str | None:
    """Return the command string from a Bash PreToolUse event, else None.

    Returns ``None`` for malformed JSON, non-dict payloads, non-Bash
    tool calls, missing ``tool_input``, non-dict ``tool_input``,
    missing or non-string ``command``, and empty command strings.
    """
    try:
        event = json.loads(stdin_text)
    except json.JSONDecodeError:
        return None
    if not isinstance(event, dict):
        return None
    if event.get("tool_name") != "Bash":
        return None
    tool_input = event.get("tool_input")
    if not isinstance(tool_input, dict):
        return None
    command = tool_input.get("command")
    if not isinstance(command, str) or not command:
        return None
    return command


def match_deny_pattern(
    stdin_text: str, patterns: list[str],
) -> tuple[str, str] | None:
    """Return ``(pattern, command)`` if a deny pattern matches, else None.

    A match is a first-token equality between any subcommand in the
    Bash event and any pattern. Returns ``None`` when *patterns* is
    empty, the event is not a Bash call, or no subcommand's first
    token equals a pattern.
    """
    if not patterns:
        return None
    command = extract_bash_command(stdin_text)
    if command is None:
        return None
    pattern_set = set(patterns)
    for token in first_tokens(command):
        if token in pattern_set:
            return (token, command)
    return None


def main(argv: list[str], stdin_text: str) -> tuple[int, str]:
    """Return ``(exit_code, stderr_text)`` for the hook invocation.

    Pure function so tests can drive every path without subprocess.
    Exits 2 with a ``"Blocked: <pattern> in <command>"`` message
    when a deny pattern matches; the command is truncated to
    ``_TRUNCATE_AT`` chars so a runaway command body cannot flood
    the tool_result the model receives.
    """
    matched = match_deny_pattern(stdin_text, argv[1:])
    if matched is None:
        return (0, "")
    pattern, command = matched
    return (2, f"Blocked: {pattern} in {command[:_TRUNCATE_AT]}")


if __name__ == "__main__":  # pragma: no cover
    _code, _stderr = main(sys.argv, sys.stdin.read())
    if _stderr:
        print(_stderr, file=sys.stderr)
    sys.exit(_code)
