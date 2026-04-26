"""Inner orchestrator for an unsatisfied LRM subclause.

Called by ``satisfy_subclause`` after ``is_subclause_satisfied`` returned
verdict ``"no"``. The script computes the subclause's dependencies,
recursively satisfies each one (excluding any cycle members already in
progress), and then dispatches to one of three mutator scripts:

  - no deps                     → satisfy_unsatisfied_subclause_without_dependencies
  - deps just satisfied         → satisfy_unsatisfied_subclause_with_satisfied_dependencies
  - cycle members co-implement  → satisfy_unsatisfied_subclause_set_with_satisfied_dependencies

Cycle detection is honest about its membership tracking: the caller
passes the in-progress set via ``--in-progress`` and the orchestrator
emits a ``{"status": "cycle", "members": [...]}`` JSON line to stdout
when it discovers a member of the in-progress set on its dependency
list. The outer orchestrator (``satisfy_subclause``) is responsible for
bubbling the cycle up to the frame that first entered any member and
dispatching the cycle-set mutator there.
"""

import argparse
import json
import subprocess
import sys

from lib.python.cli import parse_and_validate_subclause
from lib.python.satisfy.mutator import build_mutator_parser
from lib.python.satisfy.orchestrator import (
    add_in_progress_arg,
    parse_in_progress,
    run_capture,
)


_DESCRIPTION = (
    "Inner orchestrator: compute dependencies, recursively satisfy them,"
    " then dispatch to the appropriate mutator."
)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args(argv=None) -> argparse.Namespace:
    """Parse and validate CLI arguments."""
    parser = build_mutator_parser(_DESCRIPTION)
    add_in_progress_arg(parser)
    return parse_and_validate_subclause(parser, argv)


# ---------------------------------------------------------------------------
# Sub-script invocation
# ---------------------------------------------------------------------------

def invoke_compute_dependencies(
    subclause: str, lrm: str, *, model: str,
) -> list[str]:
    """Subprocess ``python -m compute_subclause_dependencies``."""
    stdout = run_capture([
        sys.executable, "-m", "compute_subclause_dependencies",
        "--lrm", lrm,
        "--subclause", subclause,
        "--model", model,
    ])
    deps = json.loads(stdout)
    if not isinstance(deps, list):
        print(
            f"compute_subclause_dependencies returned non-list: {deps}",
            file=sys.stderr,
        )
        sys.exit(1)
    return deps


def invoke_satisfy_subclause(
    subclause: str, lrm: str, *, model: str, in_progress: list[str],
) -> dict:
    """Subprocess ``python -m satisfy_subclause`` for *subclause*.

    Returns the parsed status JSON the outer orchestrator emits.
    """
    stdout = run_capture([
        sys.executable, "-m", "satisfy_subclause",
        "--lrm", lrm,
        "--subclause", subclause,
        "--model", model,
        "--in-progress", ",".join(in_progress),
    ])
    payload = json.loads(stdout) if stdout.strip() else {}
    return payload if isinstance(payload, dict) else {}


def invoke_no_deps_mutator(args: argparse.Namespace) -> None:
    """Subprocess the no-deps mutator for the current subclause."""
    cmd = [
        sys.executable, "-m",
        "satisfy_unsatisfied_subclause_without_dependencies",
        "--lrm", str(args.lrm),
        "--subclause", args.subclause,
        "--diagnostic-file", str(args.diagnostic_file),
        "--issue", str(args.issue),
        "--model", args.model,
    ]
    _run_or_die(cmd)


def invoke_with_deps_mutator(
    args: argparse.Namespace, satisfied: list[str],
) -> None:
    """Subprocess the with-deps mutator for the current subclause."""
    cmd = [
        sys.executable, "-m",
        "satisfy_unsatisfied_subclause_with_satisfied_dependencies",
        "--lrm", str(args.lrm),
        "--subclause", args.subclause,
        "--diagnostic-file", str(args.diagnostic_file),
        "--issue", str(args.issue),
        "--model", args.model,
        "--satisfied-dependencies", ",".join(satisfied),
    ]
    _run_or_die(cmd)


def _run_or_die(cmd: list[str]) -> None:
    """Run *cmd* and exit with its return code if non-zero."""
    completed = subprocess.run(cmd, check=False)
    if completed.returncode != 0:
        sys.exit(completed.returncode)


# ---------------------------------------------------------------------------
# Cycle detection and recursion
# ---------------------------------------------------------------------------

def detect_cycle_members(
    deps: list[str], in_progress: list[str],
) -> list[str]:
    """Return the subset of *deps* that already appear in *in_progress*."""
    in_progress_set = set(in_progress)
    return [d for d in deps if d in in_progress_set]


def emit_cycle_marker(subclause: str, cycle_members: list[str]) -> None:
    """Print the cycle marker JSON the outer orchestrator parses."""
    members = sorted(set(cycle_members + [subclause]))
    print(json.dumps({"status": "cycle", "members": members}))


def emit_satisfied_marker() -> None:
    """Print the satisfied-status JSON for the outer orchestrator."""
    print(json.dumps({"status": "satisfied"}))


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main(argv=None) -> None:
    """Compute deps, recurse, dispatch the right mutator."""
    args = parse_args(argv)
    in_progress = parse_in_progress(args.in_progress)
    print(
        f"Inner orchestrator: §{args.subclause}, in-progress {in_progress},"
        f" model {args.model}",
        file=sys.stderr,
    )

    deps = invoke_compute_dependencies(
        args.subclause, str(args.lrm), model=args.model,
    )
    cycle_members = detect_cycle_members(deps, in_progress)
    if cycle_members:
        emit_cycle_marker(args.subclause, cycle_members)
        return

    satisfied: list[str] = []
    extended_in_progress = in_progress + [args.subclause]
    for dep in deps:
        result = invoke_satisfy_subclause(
            dep, str(args.lrm), model=args.model,
            in_progress=extended_in_progress,
        )
        if result.get("status") == "cycle":
            members = sorted(set(result.get("members", []) + [args.subclause]))
            print(json.dumps({"status": "cycle", "members": members}))
            return
        satisfied.append(dep)

    if satisfied:
        invoke_with_deps_mutator(args, satisfied)
    else:
        invoke_no_deps_mutator(args)
    emit_satisfied_marker()
