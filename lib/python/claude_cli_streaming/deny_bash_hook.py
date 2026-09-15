import json
import re
import shlex
import sys
from fnmatch import fnmatch

_SHELL_OPERATOR_RE = re.compile(r"&&|\|\||;|\||&|\n|\r")

_LINE_BREAK_RE = re.compile(r"[\n\r]+")

_SEGMENT_BREAK_TOKENS = frozenset({
    "&&", "||", ";", ";;", "|", "|&", "&", "(", ")", "((", "))",
})

_REDIRECT_RE = re.compile(r"^[0-9]*&?[<>]{1,3}&?[0-9-]*$")

_SUBSTITUTION_RE = re.compile(r"\$\(([^()]*)\)|`([^`]*)`|<\(([^()]*)\)")

_COMPOUND_KEYWORDS = frozenset({
    "do", "then", "else", "elif", "if", "while", "until", "for",
    "{", "}", "(", ")", "{}", "!",
})

_WRAPPER_COMMANDS = frozenset({
    "caffeinate", "command", "doas", "env", "exec", "ionice", "nice",
    "nohup", "parallel", "setsid", "stdbuf", "sudo", "time", "timeout",
    "type", "unbuffer", "watch", "whence", "whereis", "which", "xargs",
})

_SHELL_COMMANDS = frozenset({
    "bash", "csh", "dash", "fish", "ksh", "sh", "tcsh", "zsh",
})

_EVAL_COMMANDS = frozenset({"eval"})

_ASSIGNMENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*=")

_NUMERIC_RE = re.compile(r"^[0-9]+(\.[0-9]+)?[smhd]?$")

_DASH_C_RE = re.compile(r"^-[a-zA-Z]*c$")

_GLOB_RE = re.compile(r"[*?\[]")

_MAX_DEPTH = 8

_TRUNCATE_AT = 80


def basename(token: str) -> str:
    return token.rstrip("/").rsplit("/", 1)[-1]


def _split_parts(segment: str) -> list[str]:
    segment = segment.strip()
    if not segment:
        return []
    try:
        return shlex.split(segment)
    except ValueError:
        return []


def _skip_prefix(parts: list[str]) -> list[str]:
    index = 0
    while index < len(parts) and (
        parts[index] in _COMPOUND_KEYWORDS
        or _ASSIGNMENT_RE.match(parts[index])
    ):
        index += 1
    return parts[index:]


def _strip_wrapper_args(parts: list[str]) -> list[str]:
    index = 0
    while index < len(parts) and (
        parts[index].startswith("-")
        or _ASSIGNMENT_RE.match(parts[index])
        or _NUMERIC_RE.match(parts[index])
    ):
        index += 1
    return parts[index:]


def _tokens_from_shell(rest: list[str], *, depth: int) -> list[str]:
    for index, token in enumerate(rest):
        if _DASH_C_RE.match(token) and index + 1 < len(rest):
            return command_tokens(rest[index + 1], depth=depth + 1)
    for token in rest:
        if not token.startswith("-"):
            return [token]
    return []


def _tokens_from_parts(parts: list[str], *, depth: int) -> list[str]:
    parts = _skip_prefix(parts)
    if not parts:
        return []
    command, rest = parts[0], parts[1:]
    tokens = [command]
    name = basename(command)
    if name in _EVAL_COMMANDS:
        tokens.extend(command_tokens(" ".join(rest), depth=depth + 1))
    elif name in _SHELL_COMMANDS:
        tokens.extend(_tokens_from_shell(rest, depth=depth))
    elif name in _WRAPPER_COMMANDS:
        tokens.extend(
            _tokens_from_parts(_strip_wrapper_args(rest), depth=depth),
        )
    return tokens


def _lex(command: str) -> list[str] | None:
    lexer = shlex.shlex(command, posix=True, punctuation_chars=True)
    lexer.whitespace_split = True
    lexer.commenters = ""
    try:
        return list(lexer)
    except ValueError:
        return None


def _segments_from_tokens(tokens: list[str]) -> list[list[str]]:
    segments: list[list[str]] = []
    current: list[str] = []
    skip_next = False
    for token in tokens:
        if skip_next:
            skip_next = False
            continue
        if token in _SEGMENT_BREAK_TOKENS:
            segments.append(current)
            current = []
        elif _REDIRECT_RE.match(token):
            skip_next = True
        else:
            current.append(token)
    segments.append(current)
    return segments


def command_tokens(command: str, *, depth: int = 0) -> list[str]:
    if depth > _MAX_DEPTH:
        return []
    tokens: list[str] = []
    for match in _SUBSTITUTION_RE.finditer(command):
        body = next(g for g in match.groups() if g is not None)
        tokens.extend(command_tokens(body, depth=depth + 1))
    outer = _LINE_BREAK_RE.sub(" ; ", _SUBSTITUTION_RE.sub(" ", command))
    lexed = _lex(outer)
    if lexed is None:
        segments = [
            _split_parts(segment)
            for segment in _SHELL_OPERATOR_RE.split(outer)
        ]
    else:
        segments = _segments_from_tokens(lexed)
    for parts in segments:
        tokens.extend(_tokens_from_parts(parts, depth=depth))
    return tokens


def match_token(token: str, patterns: list[str]) -> str | None:
    name = basename(token)
    for pattern in patterns:
        if pattern in (token, name):
            return pattern
        if _GLOB_RE.search(pattern) and (
            fnmatch(name, pattern) or fnmatch(token, pattern)
        ):
            return pattern
    return None


def extract_bash_command(stdin_text: str) -> str | None:
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
    if not patterns:
        return None
    command = extract_bash_command(stdin_text)
    if command is None:
        return None
    for token in command_tokens(command):
        pattern = match_token(token, patterns)
        if pattern is not None:
            return (pattern, command)
    return None


def main(argv: list[str], stdin_text: str) -> tuple[int, str]:
    matched = match_deny_pattern(stdin_text, argv[1:])
    if matched is None:
        return (0, "")
    pattern, command = matched
    return (2, f"Blocked: {pattern} in {command[:_TRUNCATE_AT]}")


if __name__ == "__main__":
    _code, _stderr = main(sys.argv, sys.stdin.read())
    if _stderr:
        print(_stderr, file=sys.stderr)
    sys.exit(_code)
