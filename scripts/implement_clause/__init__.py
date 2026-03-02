"""LRM clause implementation orchestrator.

Discovers subclauses, filters for implementability via Claude,
syncs a GitHub issue checklist, and invokes implement_subclause.
"""

import json
import os
import subprocess
import sys


def filter_implementable(
    clause_text: str,
    subclauses: dict[str, str],
    *,
    model: str = "sonnet",
) -> list[str]:
    """Return subclause numbers that are implementable as software."""
    numbered = "\n".join(
        f"- {k}: {v}" for k, v in subclauses.items()
    )
    prompt = (
        "You are evaluating subclauses of the IEEE SystemVerilog "
        "Language Reference Manual. Determine which of the following "
        "subclauses describe functionality that can be implemented as "
        "software (e.g., parsing, simulation, synthesis, elaboration, "
        "scheduling).\n\n"
        f"Clause text:\n{clause_text}\n\n"
        f"Subclauses:\n{numbered}\n\n"
        "Return ONLY a JSON array of the implementable subclause "
        'numbers. Example: ["4.2", "4.3"]'
    )

    env = os.environ.copy()
    env.pop("CLAUDECODE", None)

    result = subprocess.run(
        ["claude", "-p", "--model", model],
        input=prompt,
        capture_output=True,
        text=True,
        check=False,
        env=env,
    )
    if result.returncode != 0:
        print(
            f"ERROR: Claude failed:\n{result.stderr}",
            file=sys.stderr,
        )
        sys.exit(1)

    return json.loads(result.stdout.strip())
