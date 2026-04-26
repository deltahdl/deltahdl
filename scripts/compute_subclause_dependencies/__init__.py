"""Read-only dependency oracle for a single LRM subclause.

Issues a single Claude call that reads the LRM text for a subclause
and returns the ordered list of other subclauses whose satisfaction
must precede satisfaction of the input subclause. Prints the list as
JSON to stdout. Read-only: never moves, renames, edits, or deletes
anything.
"""

import json
import re
import sys

from lib.python.lrm import build_lrm_read_instruction
from lib.python.satisfy import SubclauseDependencies
from lib.python.satisfy.oracle import (
    build_oracle_args,
    extract_json_literal,
    run_oracle_call,
)


_DEP_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){0,4}$")


# ---------------------------------------------------------------------------
# Prompt construction
# ---------------------------------------------------------------------------

def build_prompt(subclause: str, lrm: str) -> str:
    """Return the single-call dependency-oracle prompt for ``subclause``."""
    read_ctx = build_lrm_read_instruction(subclause, lrm)
    return (
        f"You are the read-only dependency oracle for §{subclause}.\n\n"
        f"{read_ctx}\n\n"
        "Identify every OTHER subclause whose satisfaction is REQUIRED"
        f" before §{subclause} can be satisfied. A subclause §Y is a"
        f" dependency of §{subclause} when:\n"
        f"  - §{subclause} reuses machinery defined by §Y (binding,"
        " elaboration, configuration, etc.); OR\n"
        f"  - §{subclause} is a parent and §Y is one of its child"
        " subclauses (a parent's satisfaction rolls up over its"
        " children); OR\n"
        f"  - §{subclause}'s normative rules cannot be tested without"
        " syntax or semantics defined in §Y.\n\n"
        "Do NOT include §{subclause} itself. Do NOT include subclauses"
        " whose satisfaction is merely related, only those whose"
        " satisfaction is REQUIRED first. Order the list dependencies-"
        "first (children before parents, foundations before consumers)."
        "\n\n"
        "You are READ-ONLY. Do not move, rename, edit, create, or"
        " delete anything. Judge and report.\n\n"
        "Output ONLY a single JSON array of subclause-identifier"
        " strings, no preamble or trailing text. Each identifier is the"
        " same shape as --subclause input (digit-or-letter heads,"
        ' dotted decimal parts), e.g. ["33.6.1", "33.4.1.5"]. If there'
        " are no dependencies, output []."
    )


# ---------------------------------------------------------------------------
# Response parsing
# ---------------------------------------------------------------------------

def parse_dependencies(text: str) -> SubclauseDependencies:
    """Parse the oracle's response text into a list of subclause strings."""
    body = extract_json_literal(text)
    payload = json.loads(body)
    if not isinstance(payload, list):
        raise ValueError("Dependency oracle output must be a JSON array")
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
        result.append(item)
    return result


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

_DESCRIPTION = (
    "Read-only dependency oracle for an LRM subclause."
    " Prints a JSON array of subclause identifiers to stdout."
)


def main(argv=None) -> None:
    """Run the dependency oracle and print the JSON array to stdout."""
    args = build_oracle_args(_DESCRIPTION, argv)
    print(
        f"Dependency oracle: §{args.subclause}, model {args.model}",
        file=sys.stderr,
    )
    prompt = build_prompt(args.subclause, str(args.lrm))
    text = run_oracle_call(prompt, model=args.model)
    deps = parse_dependencies(text)
    print(json.dumps(deps, indent=2))
