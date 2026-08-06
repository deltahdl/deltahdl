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
from typing import Any, TypeAlias

from lib.python.claude_cli_streaming import (
    BUILD_TOOL_DENY_PATTERNS,
    build_env,
    build_streaming_cmd,
    exit_with_error,
    run_claude_streaming_with_retry,
    write_deny_hook_settings,
)
from lib.python.lrm import (
    build_lrm_read_instruction,
    direct_numbered_children,
    identifier_kind,
    is_sub_level_parent,
    is_top_level_aggregate,
    load_toc,
)


class IdentifierRejection(ValueError):
    """Raised when one or more dependency identifiers are turned down.

    Subclasses ``ValueError`` so the existing parse-retry loop still
    catches it. Carries the rejected identifiers so a single corrective
    turn can put every offender in front of the model: the oracle
    frequently emits several bad identifiers at once, and peeling them
    off one retry at a time burns the retry budget before all of them
    get addressed.
    """

    def __init__(self, identifiers: list[str], message: str) -> None:
        super().__init__(message)
        self.identifiers: list[str] = identifiers


class AggregateRejection(IdentifierRejection):
    """Raised when the oracle names one or more aggregate top-level entries.

    The retry-prompt builder looks up each rejected aggregate's direct
    numbered children in the TOC and presents every menu to the model
    at once — §14.12's "module, interface, program, or checker" scope
    containers come back as a bare ``["23", "24", "25", "17"]`` often
    enough that a menu per retry would not fit in the budget.
    """


class UnknownSubclauseRejection(IdentifierRejection):
    """Raised when the oracle names one or more sections the standard lacks.

    An identifier can satisfy the dotted-decimal grammar, name no
    aggregate, and still name nothing: IEEE 1800-2023 has no §23.3.7,
    though it does have §23.3.3.7 covering the dominating-net rules a
    reader would look for under that number. An identifier like that
    reaches the satisfaction pipeline, which opens a tracking issue for
    it and starts a session against a section with no text behind it.
    Such a session has no way to finish, and both of the things it can
    do instead are damaging: manufacture empty canonical files so the
    work reads as complete, or read the number as a typo and take over
    the canonical files of the similarly numbered section that another
    pass legitimately owns.
    """


SubclauseDependencies: TypeAlias = list[str]


# ---------------------------------------------------------------------------
# Claude-CLI plumbing
# ---------------------------------------------------------------------------

# Command patterns the PreToolUse hook denies for oracle sessions.
# The oracle is read-only by intent — every mutating Bash entry point
# is on this list (`git` covers commit/push/rm/mv; the on-disk shell
# mutators cover rm/mv/cp/touch/mkdir). The shared build vocabulary is
# denied too: an oracle pass runs inside the satisfaction pipeline, so
# an oracle that configured a build tree would leave exactly the mess
# the mutator's own deny list exists to prevent — and it covers the
# interpreters the oracle must not use to script around the deny list.
# PDF readers are denied because the LRM is supplied through the read-
# instruction helper, not by ad-hoc scraping.
ORACLE_DENY_PATTERNS = [
    "git", "gh",
    "rm", "mv", "cp", "touch", "mkdir",
    *BUILD_TOOL_DENY_PATTERNS,
    "pdftotext", "pdfgrep", "pdftohtml", "pdftoppm", "mutool",
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


def _checked_identifier(item: Any) -> str:
    """Return ``item`` as a subclause identifier, raising if it is not one.

    A shape failure raises rather than being collected, since an array
    carrying one has to be replaced whole before anything in it can be
    judged on what it names.
    """
    if not isinstance(item, str):
        raise ValueError(
            f"Dependency entry must be a string, got {type(item).__name__}",
        )
    if not _DEP_RE.match(item):
        raise ValueError(
            f"Dependency entry '{item}' is not a valid subclause"
            " identifier",
        )
    return item


def _aggregate_message(
    identifiers: list[str], toc: dict[str, tuple[int, int]],
) -> str:
    """Return the rejection message for identifiers naming aggregate entries.

    Each identifier is named by the word IEEE 1800-2023 uses for it,
    which :func:`lib.python.lrm.identifier_kind` reads out of ``toc``:
    §1.5 organizes the standard into clauses, and Annex A's opening sets
    annexes beside them rather than under them. Every identifier reaching
    here has passed ``is_top_level_aggregate``, so it is in ``toc`` and
    carries no dot, and the kind is therefore ``clause`` or ``annex``.
    Naming it is what tells the oracle which of the two it reached for.
    """
    named = ", ".join(
        f"{identifier_kind(ident, toc)} '{ident}'" for ident in identifiers
    )
    if len(identifiers) == 1:
        return (
            f"Dependency entry names {named}, which has numbered"
            " subclauses of its own; depend on a specific numbered"
            " subclause instead"
        )
    return (
        f"Dependency entries name {named}, which have numbered"
        " subclauses of their own; depend on specific numbered"
        " subclauses instead"
    )


def _absent_message(identifiers: list[str]) -> str:
    """Return the rejection message for identifiers naming no section.

    Joined with "or" so the one-identifier and many-identifier forms
    read as the same sentence.
    """
    quoted = " or ".join(f"'{ident}'" for ident in identifiers)
    return (
        f"No section numbered {quoted} appears in the table of contents;"
        " depend on a section number the table of contents lists"
    )


def validate_dependencies(
    payload: list[Any], *, toc: dict[str, tuple[int, int]],
) -> SubclauseDependencies:
    """Return the subclause identifiers in ``payload``, rejecting bad entries.

    ``payload`` is a decoded JSON array of dependency identifiers. It
    can reach here from a response the oracle has just produced or from
    a list recorded earlier, and both are held to the same rules: a
    stored answer is only as good as the checks it still passes.

    Rejects identifiers that name no entry in ``toc`` at all. ``toc``
    is the set of sections the standard has, so an identifier missing
    from it names a section that does not exist — well formed, not an
    aggregate, and with no text behind it for anything downstream to
    work from.

    Rejects identifiers that name an aggregate top-level entry in
    ``toc`` (a chapter or annex with at least one numbered subclause).
    Such entries are enumeration roots for a list of numbered
    subclauses, not satisfiable subclauses themselves, so a dep on one
    has no satisfaction work attached and would mislead any caller that
    treats a dep list as a queue of satisfaction prerequisites.

    Shape failures (non-string entries, identifiers that don't match
    the ``digit-or-letter head + dotted decimal parts`` grammar)
    short-circuit, since a malformed array has to be replaced whole.
    The other two are collected across the entire payload and raised at
    the end carrying every offender, so one corrective turn can put all
    of them in front of the model instead of the retry budget being
    spent an identifier at a time. Absent sections are raised ahead of
    aggregates: an aggregate rejection describes an entry ``toc``
    holds, and there is nothing to describe about an entry it does not.

    An empty ``toc`` stands the existence check down. ``load_toc``
    returns an empty table for a PDF it cannot read, which says nothing
    about which sections the standard has; judging identifiers against
    it would turn down every one of them. The stand-down is announced
    on stderr so a check that did not run does not read as one that
    passed.
    """
    if payload and not toc:
        print(
            "WARNING: the table of contents is empty, so dependency"
            " identifiers were not checked against the sections the"
            " standard has.",
            file=sys.stderr,
        )
    result: SubclauseDependencies = []
    absent: list[str] = []
    aggregates: list[str] = []
    for item in payload:
        identifier = _checked_identifier(item)
        if toc and identifier not in toc:
            absent.append(identifier)
        elif is_top_level_aggregate(identifier, toc):
            aggregates.append(identifier)
        else:
            result.append(identifier)
    if absent:
        raise UnknownSubclauseRejection(absent, _absent_message(absent))
    if aggregates:
        raise AggregateRejection(aggregates, _aggregate_message(aggregates, toc))
    return result


def parse_dependencies(
    text: str, *, toc: dict[str, tuple[int, int]],
) -> SubclauseDependencies:
    """Parse the dependency oracle's response into a list of subclause strings.

    Finds the JSON array in the oracle's output — fenced or bare, with
    or without surrounding prose — and hands the decoded array to
    :func:`validate_dependencies`, which decides which identifiers are
    acceptable. Text carrying no array at all raises, since there is
    nothing to judge.
    """
    return validate_dependencies(
        json.loads(_extract_dependency_array(text)), toc=toc,
    )


MAX_PARSE_RETRIES = 4


def build_parse_retry_prompt(
    reason: str, *,
    aggregates: list[str] | None = None,
    alternatives_map: dict[str, list[str]] | None = None,
) -> str:
    """Return the corrective prompt fed to a continued session after a parse failure.

    Embeds the rejection *reason* verbatim so the model sees which
    entry was rejected and why, then restates the array shape so the
    re-emitted answer follows the schema the parser enforces.

    When *aggregates* and *alternatives_map* are supplied (the
    aggregate-rejection branch), the prompt names every rejected
    aggregate, enumerates each aggregate's direct numbered children
    from the TOC on its own bullet, and explicitly invites listing
    more than one replacement per aggregate — the LRM often grounds a
    single rule in machinery split across multiple sibling subclauses
    (e.g. §13.3 Tasks AND §13.4 Functions both supply randsequence's
    data-passing semantics). The aggregates list preserves order so
    the model sees the menus in the same order the offenders appeared
    in its rejected array.
    """
    if aggregates is not None and alternatives_map is not None:
        quoted = ", ".join(f"'{ident}'" for ident in aggregates)
        bullets = "\n".join(
            f"- {ident}: {', '.join(alternatives_map[ident])}"
            for ident in aggregates
        )
        return (
            f"Your previous JSON array failed validation: {reason}."
            f" The rejected identifiers {quoted} each name an aggregate"
            " chapter or annex that has no rules of its own — their"
            " rules live in their numbered subclauses:\n"
            f"{bullets}\n"
            "Re-emit the array replacing every rejected aggregate with"
            " the specific numbered subclause or subclauses that carry"
            " the machinery you actually depended on; if more than one"
            " applies for a given aggregate, list all of them (the LRM"
            " frequently grounds a single rule in multiple sibling"
            " subclauses, e.g. both task and function machinery). Keep"
            " the same JSON array shape as the original prompt —"
            " digit-or-letter heads with dotted decimal parts (e.g."
            ' "13.3", "24.3"). Output an empty array [] if no remaining'
            " dependency stands."
        )
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


def build_unknown_retry_prompt(reason: str, unknown: list[str]) -> str:
    """Return the corrective prompt for identifiers naming no section.

    Embeds the rejection *reason* verbatim, names every rejected
    identifier, and points the reader at the table of contents as the
    place the real number comes from. It says out loud that a number
    close to a rejected one can exist and carry a different subject,
    because that is the way this failure usually ends: §23.3.7 read as
    the §23.3.3.7 sitting near it, whose canonical files another pass
    owns.
    """
    quoted = ", ".join(f"'{ident}'" for ident in unknown)
    return (
        f"Your previous JSON array failed validation: {reason}."
        f" The identifiers {quoted} were read as section numbers of"
        " IEEE 1800-2023, and the standard's table of contents lists no"
        " section under any of them. A number close to a rejected one"
        " can exist and carry a different subject, so read the table of"
        " contents and take the number the section you relied on"
        " actually carries. Re-emit the array with each rejected"
        " identifier replaced by that number, or with it dropped when"
        " no dependency stands behind it. Keep the digit-or-letter head"
        ' and dotted decimal parts the original prompt asked for (e.g.'
        ' "13.3", "A.7"), and output an empty array [] when no'
        " dependency remains."
    )


def _retry_prompt_for(
    exc: ValueError, toc: dict[str, tuple[int, int]],
) -> str:
    """Return the corrective prompt matching the rejection ``exc``.

    Each rejection kind has its own corrective turn: an aggregate gets
    the menu of its direct numbered children, a section the table of
    contents lacks gets pointed back at the table of contents, and
    anything else gets the plain restatement of the array shape.
    """
    if isinstance(exc, AggregateRejection):
        return build_parse_retry_prompt(
            str(exc),
            aggregates=exc.identifiers,
            alternatives_map={
                ident: direct_numbered_children(ident, toc)
                for ident in exc.identifiers
            },
        )
    if isinstance(exc, UnknownSubclauseRejection):
        return build_unknown_retry_prompt(str(exc), exc.identifiers)
    return build_parse_retry_prompt(str(exc))


def compute_subclause_dependencies(
    subclause: str, lrm: str, *, model: str, effort: str | None = None,
) -> SubclauseDependencies:
    """Run the dependency oracle for ``subclause``.

    Wraps :func:`parse_dependencies` in a corrective-feedback retry
    loop: a rejected response (malformed JSON, bad identifier shape, an
    aggregate top-level head, or a section the table of contents does
    not list) feeds the parser's rejection message back into the same
    Claude session via ``--continue`` so the model can fix the
    offending entry without re-reading the LRM. Loud-fatal once
    ``MAX_PARSE_RETRIES`` follow-ups have all failed.
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
                _retry_prompt_for(exc, toc),
                model=model, effort=effort, continue_session=True,
            )
