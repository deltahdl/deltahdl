"""Mutator for an unsatisfied subclause whose dependencies are now satisfied.

Used by the orchestrator after every dependency of §X has been
recursively satisfied. Differs from the no-deps mutator only in the
prompt context: it tells Claude which subclauses are now in place so
the model knows it can reference their machinery instead of treating
them as missing.
"""

import sys

from lib.python.cli import parse_and_validate_subclause
from lib.python.lrm import build_lrm_read_instruction
from lib.python.satisfy import SubclauseDiagnostic
from lib.python.satisfy.mutator import (
    add_dependencies_arg,
    build_failure_resolution_block,
    build_mutator_parser,
    build_no_external_state_block,
    format_diagnostic_summary,
    load_diagnostic,
    parse_satisfied_dependencies,
    run_single_subclause_mutator,
    short_circuit_if_satisfied,
)


_DESCRIPTION = (
    "Mutator: drive the codebase from oracle-says-no to oracle-says-yes"
    " for an LRM subclause whose dependencies are already satisfied."
)


def build_prompt(
    subclause: str,
    lrm: str,
    diagnostic: SubclauseDiagnostic,
    satisfied_dependencies: list[str],
) -> str:
    """Return the single-call mutator prompt for ``subclause``."""
    read_ctx = build_lrm_read_instruction(subclause, lrm)
    summary = format_diagnostic_summary(diagnostic)
    if satisfied_dependencies:
        deps_list = ", ".join(f"§{s}" for s in satisfied_dependencies)
        deps_block = (
            "DEPENDENCIES already satisfied earlier in the recursion:"
            f" {deps_list}.\n"
            "These subclauses are guaranteed to be in place — you may"
            " reference their machinery, syntax, and tests freely. Do"
            " NOT re-implement anything they already provide."
        )
    else:
        deps_block = (
            "No external dependencies needed to be satisfied first."
        )
    return (
        f"You are the mutator for §{subclause}. The satisfaction oracle"
        " has audited this subclause and produced the diagnostic below."
        " Your job is to drive the codebase from oracle-says-no to"
        " oracle-says-yes.\n\n"
        f"{read_ctx}\n\n"
        f"{deps_block}\n\n"
        f"DIAGNOSTIC for §{subclause}:\n{summary}\n\n"
        f"{build_failure_resolution_block()}\n\n"
        f"Act ONLY on requirements directly defined in §{subclause}'s"
        " LRM text. When a rule needs machinery from one of the"
        " dependencies above, reference that machinery rather than"
        " duplicating it.\n\n"
        f"{build_no_external_state_block()}"
    )


def main(argv=None) -> None:
    """Run the mutator and commit the resulting file changes."""
    parser = build_mutator_parser(_DESCRIPTION)
    add_dependencies_arg(parser)
    args = parse_and_validate_subclause(parser, argv)
    deps = parse_satisfied_dependencies(args.satisfied_dependencies)
    print(
        f"With-deps mutator: §{args.subclause}, deps {deps},"
        f" issue #{args.issue}, model {args.model}",
        file=sys.stderr,
    )
    diagnostic = load_diagnostic(args.diagnostic_file)
    if short_circuit_if_satisfied(args.subclause, diagnostic):
        return
    prompt = build_prompt(args.subclause, str(args.lrm), diagnostic, deps)
    run_single_subclause_mutator(args, prompt)
