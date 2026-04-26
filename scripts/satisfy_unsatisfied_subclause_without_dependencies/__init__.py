"""Mutator for an unsatisfied subclause that has NO dependencies.

Given the diagnostic produced by ``is_subclause_satisfied`` and a §X
that ``compute_subclause_dependencies`` returned an empty list for, this
script invokes Claude with edit permissions to address every failing
condition in the diagnostic, then commits the resulting working-tree
changes with a ``Closes #N`` trailer.

Read access to LRM text and the source/test trees is unrestricted.
Write access is limited to source/test files; ``git`` and ``gh``
commands and build/test runners are blocked at the Claude tool layer
so the script remains responsible for the commit.
"""

import sys

from lib.python.cli import parse_and_validate_subclause
from lib.python.lrm import build_lrm_read_instruction
from lib.python.satisfy import SubclauseDiagnostic
from lib.python.satisfy.mutator import (
    build_failure_resolution_block,
    build_mutator_parser,
    build_no_external_state_block,
    format_diagnostic_summary,
    load_diagnostic,
    run_single_subclause_mutator,
    short_circuit_if_satisfied,
)


_DESCRIPTION = (
    "Mutator: drive the codebase from oracle-says-no to oracle-says-yes"
    " for an LRM subclause that has no remaining dependencies."
)


def build_prompt(
    subclause: str, lrm: str, diagnostic: SubclauseDiagnostic,
) -> str:
    """Return the single-call mutator prompt for ``subclause``."""
    read_ctx = build_lrm_read_instruction(subclause, lrm)
    summary = format_diagnostic_summary(diagnostic)
    return (
        f"You are the mutator for §{subclause}. The satisfaction oracle"
        " has already audited this subclause and produced the diagnostic"
        " below. Your job is to drive the codebase from"
        " oracle-says-no to oracle-says-yes.\n\n"
        f"{read_ctx}\n\n"
        f"DIAGNOSTIC for §{subclause}:\n{summary}\n\n"
        f"{build_failure_resolution_block()}\n\n"
        f"Act ONLY on requirements directly defined in §{subclause}'s"
        " LRM text. The oracle has confirmed that this subclause has no"
        " remaining dependencies, so every failing rule is implementable"
        " with the infrastructure already in the tree.\n\n"
        f"{build_no_external_state_block()}"
    )


def main(argv=None) -> None:
    """Run the mutator and commit the resulting file changes."""
    parser = build_mutator_parser(_DESCRIPTION)
    args = parse_and_validate_subclause(parser, argv)
    print(
        f"No-deps mutator: §{args.subclause}, issue #{args.issue},"
        f" model {args.model}",
        file=sys.stderr,
    )
    diagnostic = load_diagnostic(args.diagnostic_file)
    if short_circuit_if_satisfied(args.subclause, diagnostic):
        return
    prompt = build_prompt(args.subclause, str(args.lrm), diagnostic)
    run_single_subclause_mutator(args, prompt)
