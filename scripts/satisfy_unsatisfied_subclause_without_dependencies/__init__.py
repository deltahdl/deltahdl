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
    build_mutator_parser,
    commit_mutator_result,
    format_diagnostic_summary,
    load_diagnostic,
    run_mutator_call,
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
        "For every failing condition, take the smallest set of edits"
        " that resolves it:\n"
        "  - rule_coverage failures: write production code that applies"
        " the named normative rule.\n"
        "  - test_coverage failures: write a unit test for the named"
        " normative rule, exercising the production code path.\n"
        "  - test_placement failures: move tests into the canonical"
        " files named by the diagnostic.\n"
        "  - naming failures: rename suites/tests to PascalCase"
        " descriptive names with no clause numbers.\n"
        "  - deduplication failures: delete the redundant test, keeping"
        " the canonical one.\n\n"
        f"Act ONLY on requirements directly defined in §{subclause}'s"
        " LRM text. The oracle has confirmed that §{subclause} has no"
        " dependencies, so every failing rule is implementable with the"
        " infrastructure already in the tree.\n\n"
        "Do not run git, gh, cmake, make, ctest, or pytest. Do not"
        " commit or push — the script will commit your file edits"
        " after you finish."
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
    if diagnostic.verdict == "yes":
        print(
            f"Diagnostic verdict for §{args.subclause} is already 'yes';"
            " nothing to do.",
            file=sys.stderr,
        )
        return
    prompt = build_prompt(args.subclause, str(args.lrm), diagnostic)
    run_mutator_call(prompt, model=args.model)
    if not commit_mutator_result([args.subclause], [args.issue]):
        print(
            f"Mutator for §{args.subclause} produced no source-tree"
            " changes; nothing committed.",
            file=sys.stderr,
        )
