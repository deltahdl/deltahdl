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

Patterns are command names (e.g. ``cmake``, ``make``) or globs over a
command name or its full path (e.g. ``clang*``, ``*.sh``,
``build*/*``). Matching is deliberately not a bare first-token
equality: a sub-Claude that wanted to build found every hole in that
rule, so the scan now walks each *command position* in the Bash
string and compares both the token as written and its basename:

  - quote-aware operator splitting (``&&``, ``||``, ``;``, ``|``, ``&``,
    newlines) so ``cd /tmp && cmake .`` is caught while a quoted
    payload stays in one piece;
  - basename comparison so ``/opt/homebrew/bin/cmake`` and
    ``/usr/bin/clang++`` are caught, not just bare ``cmake``;
  - wrapper unwrapping (``env``, ``time``, ``timeout``, ``xargs``,
    ``sudo``, ``nohup``, …) so ``env NINJA=… ninja -C build`` and
    ``timeout 600 make`` are caught;
  - shell unwrapping so ``bash -c "cmake ."`` is caught by recursing
    into the ``-c`` argument, and ``bash rebuild.sh`` is caught by
    treating the script path as a command position;
  - ``eval`` unwrapping so ``eval "cmake ."`` is caught by rejoining
    its operands and re-parsing them;
  - ``#`` treated as an ordinary character, so a comment cannot cut
    the scan short of the commands that follow it;
  - command-substitution recursion so ``$(which cmake) -S .`` and
    ``` `make` ``` are caught;
  - leading environment assignments and compound-command keywords
    (``do``, ``then``, ``if``, ``{}``, …) are skipped so the command
    they introduce is what gets compared.

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
from fnmatch import fnmatch

# Fallback splitter, used only when the quote-aware lexer rejects the
# string (e.g. an unclosed quote). Splitting the raw text this way is
# what the hook used to do everywhere, and it is why `bash -c "cd /repo
# && make"` escaped: the `&&` inside the quoted payload shredded the
# string into two unparseable halves that were then both skipped.
_SHELL_OPERATOR_RE = re.compile(r"&&|\|\||;|\||&|\n|\r")

_LINE_BREAK_RE = re.compile(r"[\n\r]+")

# Token forms that end one command and start the next.
_SEGMENT_BREAK_TOKENS = frozenset({
    "&&", "||", ";", ";;", "|", "|&", "&", "(", ")", "((", "))",
})

# Redirections (`>`, `>>`, `2>`, `<`, `>&`, …). The token after one is a
# file, not a command, so it is skipped rather than treated as the head
# of a new segment.
_REDIRECT_RE = re.compile(r"^[0-9]*&?[<>]{1,3}&?[0-9-]*$")

# ``$(...)``, ``` `...` ``` and ``<(...)``. Non-nesting on purpose: the
# inner body of a nested substitution is itself matched by a later
# iteration of ``finditer``, so no command position is lost.
_SUBSTITUTION_RE = re.compile(r"\$\(([^()]*)\)|`([^`]*)`|<\(([^()]*)\)")

# Compound-command keywords and group openers that can precede the real
# command inside a segment (e.g. ``do git add`` in a ``for`` loop body,
# ``{}`` in an ``xargs -I {}`` template). Skipping a leading run of these
# reaches the command they introduce.
_COMPOUND_KEYWORDS = frozenset({
    "do", "then", "else", "elif", "if", "while", "until", "for",
    "{", "}", "(", ")", "{}", "!",
})

# Commands that run — or resolve the path of — another command given as
# their argument. The token after the wrapper's own flags is itself a
# command position. The lookup tools (`which`, `type`, …) are included
# because `$(which cmake) -S .` otherwise launders the name past the
# scan as a mere argument.
_WRAPPER_COMMANDS = frozenset({
    "caffeinate", "command", "doas", "env", "exec", "ionice", "nice",
    "nohup", "parallel", "setsid", "stdbuf", "sudo", "time", "timeout",
    "type", "unbuffer", "watch", "whence", "whereis", "which", "xargs",
})

# Shells: ``-c`` takes a whole command string, and a bare argument is a
# script path — both are command positions.
_SHELL_COMMANDS = frozenset({
    "bash", "csh", "dash", "fish", "ksh", "sh", "tcsh", "zsh",
})

# ``eval`` joins its operands into one command string and runs that, so
# the whole operand list is a command position once rejoined and
# re-parsed. Neither of the rules above reaches it: the wrapper rule
# leaves ``eval "cmake ."`` holding a single unparsed token, and the
# shell rule finds no ``-c`` to key on.
_EVAL_COMMANDS = frozenset({"eval"})

_ASSIGNMENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*=")

# A wrapper's non-flag operand that is a duration or count rather than a
# command (``timeout 600 make``, ``nice -n 10 make``).
_NUMERIC_RE = re.compile(r"^[0-9]+(\.[0-9]+)?[smhd]?$")

# ``-c``, and clustered forms such as ``-lc`` / ``-ec``.
_DASH_C_RE = re.compile(r"^-[a-zA-Z]*c$")

_GLOB_RE = re.compile(r"[*?\[]")

# Bounds the recursion that re-parses one string as another command
# (a substitution body, a ``sh -c`` payload) so a pathological command
# cannot spin the hook.
_MAX_DEPTH = 8

_TRUNCATE_AT = 80


def basename(token: str) -> str:
    """Return the last path component of *token*.

    ``/opt/homebrew/bin/cmake`` and ``./scratchpad/rebuild.sh`` reduce
    to ``cmake`` and ``rebuild.sh`` so a deny pattern written as a bare
    command name still matches an absolute or relative invocation.
    """
    return token.rstrip("/").rsplit("/", 1)[-1]


def _split_parts(segment: str) -> list[str]:
    """Return the shlex tokens of *segment*, or ``[]`` if unparseable.

    Empty / whitespace-only segments and segments shlex cannot parse
    (e.g. unclosed quotes) yield ``[]`` so callers skip them.
    """
    segment = segment.strip()
    if not segment:
        return []
    try:
        return shlex.split(segment)
    except ValueError:
        return []


def _skip_prefix(parts: list[str]) -> list[str]:
    """Drop leading compound keywords and environment assignments."""
    index = 0
    while index < len(parts) and (
        parts[index] in _COMPOUND_KEYWORDS
        or _ASSIGNMENT_RE.match(parts[index])
    ):
        index += 1
    return parts[index:]


def _strip_wrapper_args(parts: list[str]) -> list[str]:
    """Drop a wrapper's own flags, assignments, and numeric operands.

    What remains starts at the command the wrapper runs — ``make`` in
    ``timeout 600 make``, ``ninja`` in ``env NINJA=1 ninja -C build``.
    """
    index = 0
    while index < len(parts) and (
        parts[index].startswith("-")
        or _ASSIGNMENT_RE.match(parts[index])
        or _NUMERIC_RE.match(parts[index])
    ):
        index += 1
    return parts[index:]


def _tokens_from_shell(rest: list[str], *, depth: int) -> list[str]:
    """Return the command positions a shell invocation introduces.

    ``-c`` (or a clustered ``-lc``) is followed by a command string,
    which is re-parsed in full; otherwise the first non-flag operand is
    a script path and is itself a command position.
    """
    for index, token in enumerate(rest):
        if _DASH_C_RE.match(token) and index + 1 < len(rest):
            return command_tokens(rest[index + 1], depth=depth + 1)
    for token in rest:
        if not token.startswith("-"):
            return [token]
    return []


def _tokens_from_parts(parts: list[str], *, depth: int) -> list[str]:
    """Return every command position reachable from one segment's tokens.

    Unwrapping a wrapper recurses on a strictly shorter parts list, so
    that recursion terminates on its own and is deliberately not
    depth-bounded — bounding it would let a long wrapper chain
    (``env env env … cmake``) run off the end of the scan. Re-parsing a
    shell payload or an ``eval`` operand list is a different matter:
    that goes back through ``command_tokens``, which carries the depth
    bound.
    """
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
    """Return quote-aware tokens for *command*, or ``None`` if unparseable.

    ``punctuation_chars`` makes shlex emit ``&&``, ``||``, ``;``, ``|``,
    ``&``, and the redirection characters as tokens of their own while
    keeping a quoted payload — the argument of ``bash -c`` — intact as a
    single token, which a raw-text split cannot do.

    Clearing ``commenters`` keeps ``#`` an ordinary character. shlex
    otherwise discards everything from an unquoted ``#`` to the end of
    the string, and since the caller has already rewritten newlines as
    ``;`` separators by this point, a comment on the first line would
    take every command after it out of the scan.
    """
    lexer = shlex.shlex(command, posix=True, punctuation_chars=True)
    lexer.whitespace_split = True
    lexer.commenters = ""
    try:
        return list(lexer)
    except ValueError:
        return None


def _segments_from_tokens(tokens: list[str]) -> list[list[str]]:
    """Split a lexed token list into one parts-list per command."""
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
    """Return every command-position token inside *command*.

    Command substitutions are scanned first (and blanked out of the
    outer string so their leftovers cannot confuse the lexer); newlines
    become explicit separators; the remainder is lexed quote-aware and
    split into segments, and each segment contributes its command plus
    anything that command wraps. A string the lexer rejects falls back
    to the raw-text operator split so a malformed command still gets a
    best-effort scan. Empty and keyword-only segments contribute
    nothing.
    """
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
    """Return the first pattern *token* matches, else ``None``.

    A pattern matches on equality with the token as written or with its
    basename; a pattern containing ``*``, ``?``, or ``[`` is additionally
    fnmatched against both, so ``clang*`` covers ``/usr/bin/clang++``
    and ``build*/*`` covers ``build-b2debug/bin/test_parser``.
    """
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

    A match is any command position in the Bash event matching any
    pattern under ``match_token``. Returns ``None`` when *patterns* is
    empty, the event is not a Bash call, or no command position matches.
    """
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
