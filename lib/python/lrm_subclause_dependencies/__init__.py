"""Read-only dependency oracle for LRM subclauses.

A single oracle: ``compute_subclause_dependencies`` returns a
``SubclauseDependencies`` list of subclause identifiers ordered
foundations-first.

The invocation is read-only: the disallowed-tools list blocks every
mutating tool and ``run_oracle_call`` exits non-zero on any failure.
"""

import json
import os
import re
import sys
from typing import TypeAlias

from lib.python.claude_cli_streaming import (
    build_env,
    build_streaming_cmd,
    exit_with_error,
    run_claude_streaming_with_retry,
    write_deny_hook_settings,
)
from lib.python.lrm import (
    build_lrm_read_instruction,
    is_sub_level_parent,
    is_top_level_aggregate,
    load_toc,
)


SubclauseDependencies: TypeAlias = list[str]


# ---------------------------------------------------------------------------
# Claude-CLI plumbing
# ---------------------------------------------------------------------------

# Bare-command patterns the PreToolUse hook denies for oracle sessions.
# The oracle is read-only by intent — every mutating Bash entry point
# is on this list (`git` covers commit/push/rm/mv; the on-disk shell
# mutators cover rm/mv/cp/touch/mkdir). Python interpreters are denied
# so the oracle cannot execute scripts to bypass the deny list. PDF
# readers are denied because the LRM is supplied through the read-
# instruction helper, not by ad-hoc scraping.
ORACLE_DENY_PATTERNS = [
    "git", "gh",
    "rm", "mv", "cp", "touch", "mkdir",
    "pdftotext", "pdfgrep", "pdftohtml", "pdftoppm", "mutool",
    "python", "python3",
]


def run_oracle_call(
    prompt: str,
    *,
    model: str,
    effort: str | None = None,
    continue_session: bool = False,
) -> str:
    """Invoke Claude with read-only tools; return the oracle's ``.result``.

    Runs the CLI in stream-json mode so the streaming runner can decode
    events and print Claude's text/tool_use blocks live — oracle passes
    can take many minutes and the user needs to see progress. Wraps
    each call in a content-filter retry loop (max two retries) using
    the recovery prompt from the streaming runner; the retry call
    appends ``--continue`` so it resumes the same Claude session.
    Loud-fatal on a non-zero exit code, a missing result event, or
    after the retry budget is exhausted. When *effort* is set, the
    Claude CLI runs at that thinking-budget tier; the retry cmd
    carries the same effort so the recovery call matches the original
    session's shape. When *continue_session* is true, the initial cmd
    also appends ``--continue`` so the call resumes the most recent
    Claude session rather than starting a fresh one — used by the
    parse-retry loop in ``compute_subclause_dependencies`` to feed
    corrective feedback into the same session that produced the
    rejected response.

    A fresh ``settings.json`` is written for each call wiring the
    PreToolUse Bash deny hook with ``ORACLE_DENY_PATTERNS``; the file
    is removed once the call returns.
    """
    settings_path = write_deny_hook_settings(ORACLE_DENY_PATTERNS)
    try:
        cmd = build_streaming_cmd(
            model=model, settings_path=settings_path,
            continue_session=continue_session, effort=effort,
        )
        retry_cmd = build_streaming_cmd(
            model=model, settings_path=settings_path,
            continue_session=True, effort=effort,
        )
        return run_claude_streaming_with_retry(
            cmd, prompt, env=build_env(), retry_cmd=retry_cmd, role="Oracle",
        )
    finally:
        os.unlink(settings_path)


# ---------------------------------------------------------------------------
# compute_subclause_dependencies
# ---------------------------------------------------------------------------

_DEP_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){0,4}$")
_FENCED_ARR_RE = re.compile(r"```(?:json)?\s*(\[.*?\])\s*```", re.DOTALL)
_BARE_ARR_RE = re.compile(r"\[[^\[\]]*\]", re.DOTALL)


def _extract_dependency_array(text: str) -> str:
    """Return a JSON array substring from the dependency oracle's output."""
    match = _FENCED_ARR_RE.search(text)
    if match:
        return match.group(1)
    # Pick the LAST bare-array group: the oracle's reasoning prose can
    # contain bracketed examples (e.g. "[example with typedef struct,
    # function]") earlier in the response, so a greedy match would span
    # from the first prose bracket to the actual final answer.
    matches: list[str] = _BARE_ARR_RE.findall(text)
    if matches:
        return matches[-1]
    raise ValueError("No JSON array found in oracle output")


def build_dependency_prompt(subclause: str, lrm: str) -> str:
    """Return the single-call dependency-oracle prompt for ``subclause``.

    For a sub-level parent — a target that has its own preamble rules
    and contains named numbered subclauses below it — the prompt
    anchors the dependency answer in the preamble alone, since the
    numbered subclauses are queried separately as their own targets.
    For every other target the prompt asks about the subclause's own
    rules directly.
    """
    read_ctx = build_lrm_read_instruction(subclause, lrm)
    toc = load_toc(lrm)
    if is_sub_level_parent(subclause, toc):
        builder = f"§{subclause}'s preamble"
        citation = f"§{subclause}'s preamble"
        scope_note = (
            f"§{subclause} contains named numbered subclauses below it;"
            " those numbered subclauses are queried separately, so"
            " anchor your answer in the normative rules stated by"
            f" §{subclause}'s own preamble.\n\n"
        )
    else:
        builder = f"§{subclause}'s implementation"
        citation = f"§{subclause}"
        scope_note = ""
    return (
        f"You are the read-only dependency oracle for §{subclause}.\n\n"
        f"{read_ctx}\n\n"
        f"{scope_note}"
        f"List the subclauses {builder} builds on top of. A subclause"
        f" §Y belongs on the list when {citation} states a normative"
        " rule whose implementation needs §Y's machinery to already be"
        " in place. For each subclause you list, you can quote the"
        f" sentence in {citation} that states the rule and name the §Y"
        " machinery the rule needs.\n\n"
        "Order the list foundations-first: subclauses that define the"
        " most general machinery come before subclauses that build on"
        " those.\n\n"
        "Read-only role: judge and report.\n\n"
        "Output a single JSON array of subclause-identifier strings"
        " in the same shape as --subclause input (digit-or-letter"
        ' heads, dotted decimal parts), e.g. ["33.6.1", "33.4.1.5"].'
        f" An empty array [] means {citation}'s normative rules"
        " implement on top of code already in the tree."
    )


def parse_dependencies(
    text: str, *, toc: dict[str, tuple[int, int]],
) -> SubclauseDependencies:
    """Parse the dependency oracle's response into a list of subclause strings.

    Rejects identifiers that name an aggregate top-level entry in
    ``toc`` (a chapter or annex with at least one numbered subclause).
    Such entries are enumeration roots for a list of numbered
    subclauses, not satisfiable subclauses themselves, so a dep on one
    has no satisfaction work attached and would mislead any caller that
    treats a dep list as a queue of satisfaction prerequisites.
    """
    body = _extract_dependency_array(text)
    payload = json.loads(body)
    result: SubclauseDependencies = []
    for item in payload:
        if not isinstance(item, str):
            raise ValueError(
                f"Dependency entry must be a string, got {type(item).__name__}",
            )
        if not _DEP_RE.match(item):
            raise ValueError(
                f"Dependency entry '{item}' is not a valid subclause"
                " identifier",
            )
        if is_top_level_aggregate(item, toc):
            raise ValueError(
                f"Dependency entry '{item}' names an aggregate top-level"
                " entry; depend on a specific numbered subclause instead",
            )
        result.append(item)
    return result


MAX_PARSE_RETRIES = 2


def build_parse_retry_prompt(reason: str) -> str:
    """Return the corrective prompt fed to a continued session after a parse failure.

    Embeds the rejection *reason* verbatim so the model sees which
    entry was rejected and why, then restates the array shape so the
    re-emitted answer follows the schema the parser enforces.
    """
    return (
        f"Your previous JSON array failed validation: {reason}."
        " Re-emit a single JSON array of subclause-identifier strings"
        " in the same shape as the original prompt — digit-or-letter"
        ' heads with dotted decimal parts (e.g. "33.6.1", "A.7").'
        " An aggregate top-level chapter or annex head with no dotted"
        ' tail (a bare "8" or "A") is invalid; depend on a specific'
        ' numbered subclause like "8.1" instead. Output an empty array'
        " [] if the rejected list was wrong and there are no genuine"
        " dependencies left."
    )


def compute_subclause_dependencies(
    subclause: str, lrm: str, *, model: str, effort: str | None = None,
) -> SubclauseDependencies:
    """Run the dependency oracle for ``subclause``.

    Wraps :func:`parse_dependencies` in a corrective-feedback retry
    loop: a rejected response (malformed JSON, bad identifier shape, or
    an aggregate top-level head) feeds the parser's rejection message
    back into the same Claude session via ``--continue`` so the model
    can fix the offending entry without re-reading the LRM. Loud-fatal
    once ``MAX_PARSE_RETRIES`` follow-ups have all failed.
    """
    print(
        f"Dependency oracle: §{subclause}, model {model}",
        file=sys.stderr,
    )
    toc = load_toc(lrm)
    text = run_oracle_call(
        build_dependency_prompt(subclause, lrm), model=model, effort=effort,
    )
    follow_ups = 0
    while True:
        try:
            return parse_dependencies(text, toc=toc)
        except ValueError as exc:
            follow_ups += 1
            if follow_ups > MAX_PARSE_RETRIES:
                exit_with_error(
                    f"Dependency oracle parse failed for §{subclause}"
                    f" after {MAX_PARSE_RETRIES + 1} attempts: {exc}",
                    "",
                )
            print(
                f"WARNING: Dependency oracle parse failed for §{subclause}"
                f" (attempt {follow_ups}): {exc};"
                " retrying with corrective feedback.",
                file=sys.stderr,
            )
            text = run_oracle_call(
                build_parse_retry_prompt(str(exc)),
                model=model, effort=effort, continue_session=True,
            )
