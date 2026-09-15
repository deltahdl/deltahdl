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
    def __init__(self, identifiers: list[str], message: str) -> None:
        super().__init__(message)
        self.identifiers: list[str] = identifiers


class AggregateRejection(IdentifierRejection):
    pass


class UnknownSubclauseRejection(IdentifierRejection):
    pass


SubclauseDependencies: TypeAlias = list[str]


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


_DEP_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){0,4}$")
_FENCED_ARR_RE = re.compile(r"```(?:json)?\s*(\[.*?\])\s*```", re.DOTALL)
_BARE_ARR_RE = re.compile(r"\[[^\[\]]*\]", re.DOTALL)


def _extract_dependency_array(text: str) -> str:
    match = _FENCED_ARR_RE.search(text)
    if match:
        return match.group(1)
    matches: list[str] = _BARE_ARR_RE.findall(text)
    if matches:
        return matches[-1]
    raise ValueError("No JSON array found in oracle output")


def build_dependency_prompt(subclause: str, lrm: str) -> str:
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
    quoted = " or ".join(f"'{ident}'" for ident in identifiers)
    return (
        f"No section numbered {quoted} appears in the table of contents;"
        " depend on a section number the table of contents lists"
    )


def validate_dependencies(
    payload: list[Any], *, toc: dict[str, tuple[int, int]],
) -> SubclauseDependencies:
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
    return validate_dependencies(
        json.loads(_extract_dependency_array(text)), toc=toc,
    )


MAX_PARSE_RETRIES = 4


def build_parse_retry_prompt(
    reason: str, *,
    aggregates: list[str] | None = None,
    alternatives_map: dict[str, list[str]] | None = None,
) -> str:
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
