"""Mutator for a CYCLE of unsatisfied subclauses (co-implementation).

The orchestrator dispatches to this script when ``compute_subclause_dependencies``
detects a dependency cycle of two or three subclauses (per the cap in
#1265). Each cycle member's external dependencies (the union of each
member's deps minus the cycle members themselves) are already satisfied
by the time control reaches this script, so the only remaining work is
to co-implement the members in a single mutator invocation. The commit
carries one ``Closes #N`` trailer per member.
"""

import argparse
import sys
from pathlib import Path

from lib.python.cli import (
    add_lrm_arg,
    add_model_arg,
    parse_and_validate,
)
from lib.python.lrm import build_lrm_read_instruction
from lib.python.satisfy import SubclauseDiagnostic
from lib.python.satisfy.mutator import (
    add_dependencies_arg,
    build_failure_resolution_block,
    build_no_external_state_block,
    commit_mutator_result,
    format_diagnostic_summary,
    load_diagnostic,
    parse_satisfied_dependencies,
    run_mutator_call,
)


_DESCRIPTION = (
    "Mutator: co-implement a 2- or 3-member dependency cycle whose"
    " external dependencies are already satisfied."
)

_MAX_CYCLE_MEMBERS = 3


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _parse_csv(raw: str) -> list[str]:
    """Split a comma-separated argument into stripped non-empty strings."""
    return [item.strip() for item in raw.split(",") if item.strip()]


def parse_args(argv=None) -> argparse.Namespace:
    """Parse and validate CLI arguments for the cycle-set mutator."""
    parser = argparse.ArgumentParser(description=_DESCRIPTION)
    add_lrm_arg(parser)
    parser.add_argument(
        "--subclauses",
        type=_parse_csv,
        required=True,
        help="Comma-separated cycle members, e.g. '33.4.1.5,33.4.1.6'.",
    )
    parser.add_argument(
        "--diagnostic-files",
        type=lambda raw: [Path(p) for p in _parse_csv(raw)],
        required=True,
        help="Comma-separated diagnostic-file paths, one per cycle member.",
    )
    parser.add_argument(
        "--issues",
        type=lambda raw: [int(s) for s in _parse_csv(raw)],
        required=True,
        help="Comma-separated GitHub issue numbers, one per cycle member.",
    )
    add_dependencies_arg(parser)
    add_model_arg(parser)
    args = parse_and_validate(parser, argv)

    if not 2 <= len(args.subclauses) <= _MAX_CYCLE_MEMBERS:
        parser.error(
            f"Cycle must have 2 or {_MAX_CYCLE_MEMBERS} members (got"
            f" {len(args.subclauses)}). Larger cycles are surfaced to"
            " humans via the pipeline-cycle label.",
        )
    if (len(args.diagnostic_files) != len(args.subclauses)
            or len(args.issues) != len(args.subclauses)):
        parser.error(
            "--subclauses, --diagnostic-files and --issues must all have"
            " the same number of entries.",
        )
    return args


# ---------------------------------------------------------------------------
# Prompt construction
# ---------------------------------------------------------------------------

def build_prompt(
    subclauses: list[str],
    lrm: str,
    diagnostics: list[SubclauseDiagnostic],
    satisfied_dependencies: list[str],
) -> str:
    """Return the single-call cycle-set mutator prompt."""
    members = ", ".join(f"§{s}" for s in subclauses)
    read_instructions = "\n\n".join(
        build_lrm_read_instruction(s, lrm) for s in subclauses
    )
    diagnostic_blocks = "\n\n".join(
        f"DIAGNOSTIC for §{s}:\n{format_diagnostic_summary(d)}"
        for s, d in zip(subclauses, diagnostics)
    )
    if satisfied_dependencies:
        deps_list = ", ".join(f"§{s}" for s in satisfied_dependencies)
        deps_block = (
            "EXTERNAL dependencies (outside the cycle) already satisfied:"
            f" {deps_list}."
        )
    else:
        deps_block = (
            "No external dependencies needed to be satisfied first."
        )
    return (
        f"You are the cycle co-implementation mutator for {members}."
        " These subclauses form a dependency cycle: each one requires"
        " machinery from the others, so they must be implemented"
        " together in a single pass.\n\n"
        f"{read_instructions}\n\n"
        f"{deps_block}\n\n"
        f"{diagnostic_blocks}\n\n"
        f"{build_failure_resolution_block()}\n\n"
        "When fixing one member, you may freely reference syntax and"
        " machinery defined by another cycle member — that is the"
        " whole reason this is a co-implementation. Do not split the"
        " edits into separate passes.\n\n"
        f"{build_no_external_state_block()}"
    )


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main(argv=None) -> None:
    """Run the cycle-set mutator and commit the resulting changes."""
    args = parse_args(argv)
    deps = parse_satisfied_dependencies(args.satisfied_dependencies)
    print(
        f"Cycle-set mutator: subclauses {args.subclauses},"
        f" external deps {deps}, issues {args.issues},"
        f" model {args.model}",
        file=sys.stderr,
    )
    diagnostics = [load_diagnostic(p) for p in args.diagnostic_files]
    if all(d.verdict == "yes" for d in diagnostics):
        print(
            "Every cycle member already has verdict 'yes'; nothing to do.",
            file=sys.stderr,
        )
        return
    prompt = build_prompt(args.subclauses, str(args.lrm), diagnostics, deps)
    run_mutator_call(prompt, model=args.model)
    if not commit_mutator_result(args.subclauses, args.issues):
        print(
            f"Cycle-set mutator for {args.subclauses} produced no source"
            "-tree changes; nothing committed.",
            file=sys.stderr,
        )
