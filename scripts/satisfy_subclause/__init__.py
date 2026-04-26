"""Outer orchestrator and user-facing entry point for the satisfy pipeline.

``satisfy_subclause --subclause X --lrm path`` is idempotent: if §X is
already satisfied (per ``is_subclause_satisfied``), it does nothing.
Otherwise:

  1. Run ``is_subclause_satisfied`` to obtain a SubclauseDiagnostic.
  2. If verdict is "yes": exit successfully.
  3. Otherwise, ensure a GitHub issue exists for §X (create or reopen),
     then invoke ``satisfy_unsatisfied_subclause`` to either dispatch a
     mutator or to surface a cycle marker.
  4. If a cycle marker bubbles up here, dispatch the cycle-set mutator
     for the cycle members.
  5. Re-run the oracle. If verdict still "no", retry the inner pipeline
     ONCE with the fresh diagnostic. If still "no" after the retry,
     label the issue with ``pipeline-stuck``, post the final diagnostic
     as a comment, and exit non-zero.

The outer orchestrator threads ``--in-progress`` so the inner
orchestrator can detect dependency cycles, and intentionally subprocesses
each delegate (oracle, inner orchestrator, mutators) so each step runs
in its own bounded Claude context.
"""

import argparse
import json
import subprocess
import sys
import tempfile
from dataclasses import asdict
from pathlib import Path

from lib.python.cli import (
    add_lrm_arg,
    add_model_arg,
    add_subclause_arg,
    parse_and_validate_subclause,
)
from lib.python.satisfy import SubclauseDiagnostic
from lib.python.satisfy.orchestrator import (
    add_in_progress_arg,
    parse_in_progress,
    run_capture,
)


_DESCRIPTION = (
    "Outer orchestrator: idempotently satisfy an LRM subclause."
    " Runs the oracle, dispatches the mutator pipeline if needed,"
    " and labels the issue pipeline-stuck if a single retry does not"
    " converge."
)

_MAX_RETRIES = 1


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args(argv=None) -> argparse.Namespace:
    """Parse and validate CLI arguments."""
    parser = argparse.ArgumentParser(description=_DESCRIPTION)
    add_lrm_arg(parser)
    add_subclause_arg(parser)
    add_model_arg(parser)
    add_in_progress_arg(parser)
    return parse_and_validate_subclause(parser, argv)


# ---------------------------------------------------------------------------
# Sub-script invocation
# ---------------------------------------------------------------------------

def invoke_oracle(
    subclause: str, lrm: str, *, model: str,
) -> SubclauseDiagnostic:
    """Subprocess ``python -m is_subclause_satisfied`` and parse output."""
    stdout = run_capture([
        sys.executable, "-m", "is_subclause_satisfied",
        "--lrm", lrm, "--subclause", subclause, "--model", model,
    ])
    payload = json.loads(stdout)
    return SubclauseDiagnostic(
        rule_coverage=payload["rule_coverage"],
        test_coverage=payload["test_coverage"],
        test_placement=payload["test_placement"],
        naming=payload["naming"],
        deduplication=payload["deduplication"],
    )


def invoke_inner_orchestrator(
    args: argparse.Namespace, diagnostic_path: Path, issue: int,
    in_progress: list[str],
) -> dict:
    """Subprocess the inner orchestrator; return its status JSON."""
    cmd = [
        sys.executable, "-m", "satisfy_unsatisfied_subclause",
        "--lrm", str(args.lrm),
        "--subclause", args.subclause,
        "--diagnostic-file", str(diagnostic_path),
        "--issue", str(issue),
        "--model", args.model,
        "--in-progress", ",".join(in_progress),
    ]
    stdout = run_capture(cmd)
    payload = json.loads(stdout) if stdout.strip() else {}
    return payload if isinstance(payload, dict) else {}


def invoke_cycle_mutator(
    args: argparse.Namespace,
    members: list[str],
    diagnostic_paths: list[Path],
    issues: list[int],
) -> None:
    """Subprocess the cycle-set mutator for *members*."""
    cmd = [
        sys.executable, "-m",
        "satisfy_unsatisfied_subclause_set_with_satisfied_dependencies",
        "--lrm", str(args.lrm),
        "--subclauses", ",".join(members),
        "--diagnostic-files", ",".join(str(p) for p in diagnostic_paths),
        "--issues", ",".join(str(i) for i in issues),
        "--model", args.model,
        "--satisfied-dependencies", "",
    ]
    completed = subprocess.run(cmd, check=False)
    if completed.returncode != 0:
        sys.exit(completed.returncode)


def dispatch_cycle(
    args: argparse.Namespace, members: list[str], workdir: Path,
) -> None:
    """Gather per-member diagnostics and issues, then run the cycle mutator."""
    diagnostics: list[Path] = []
    issues: list[int] = []
    for member in members:
        diag = invoke_oracle(member, str(args.lrm), model=args.model)
        path = workdir / f"diag_{member.replace('.', '_')}.json"
        path.write_text(json.dumps(asdict(diag)), encoding="utf-8")
        diagnostics.append(path)
        issues.append(find_or_create_issue(member))
    invoke_cycle_mutator(args, members, diagnostics, issues)


# ---------------------------------------------------------------------------
# GitHub issue handling
# ---------------------------------------------------------------------------

def issue_title_for(subclause: str) -> str:
    """Return the canonical GitHub issue title for *subclause*."""
    return f"Satisfy §{subclause}"


def find_or_create_issue(subclause: str) -> int:
    """Return the issue number for *subclause* (creating or reopening)."""
    title = issue_title_for(subclause)
    completed = subprocess.run(
        [
            "gh", "issue", "list",
            "--state", "all",
            "--search", title,
            "--json", "number,title,state",
        ],
        capture_output=True, text=True, check=False,
    )
    if completed.returncode != 0:
        print(completed.stderr, file=sys.stderr)
        sys.exit(completed.returncode)
    matches = json.loads(completed.stdout) if completed.stdout.strip() else []
    for entry in matches:
        if entry.get("title") == title:
            number = int(entry["number"])
            if entry.get("state", "").lower() == "closed":
                subprocess.run(
                    ["gh", "issue", "reopen", str(number)],
                    check=False,
                )
            return number
    completed = subprocess.run(
        [
            "gh", "issue", "create",
            "--title", title,
            "--body", (
                f"Track satisfying §{subclause} via the satisfaction"
                " pipeline (#1265)."
            ),
        ],
        capture_output=True, text=True, check=False,
    )
    if completed.returncode != 0:
        print(completed.stderr, file=sys.stderr)
        sys.exit(completed.returncode)
    return parse_issue_number_from_create_output(completed.stdout)


def parse_issue_number_from_create_output(output: str) -> int:
    """Extract the issue number from a ``gh issue create`` URL."""
    url = output.strip().splitlines()[-1].strip()
    return int(url.rsplit("/", 1)[-1])


def label_issue_pipeline_stuck(
    issue: int, diagnostic: SubclauseDiagnostic,
) -> None:
    """Add the pipeline-stuck label and post the final diagnostic comment."""
    subprocess.run(
        ["gh", "issue", "edit", str(issue),
         "--add-label", "pipeline-stuck"],
        check=False,
    )
    body = "Pipeline stuck after retry. Final diagnostic:\n```json\n" \
        + json.dumps(asdict(diagnostic), indent=2) + "\n```\n"
    subprocess.run(
        ["gh", "issue", "comment", str(issue), "--body", body],
        check=False,
    )


# ---------------------------------------------------------------------------
# Pipeline
# ---------------------------------------------------------------------------

def write_diagnostic(directory: Path, diagnostic: SubclauseDiagnostic) -> Path:
    """Serialise *diagnostic* to a JSON file under *directory*."""
    path = directory / "diagnostic.json"
    path.write_text(json.dumps(asdict(diagnostic)), encoding="utf-8")
    return path


def emit_status(payload: dict) -> None:
    """Print a status JSON payload to stdout (consumed by the inner orch)."""
    print(json.dumps(payload))


def run_pipeline_pass(
    args: argparse.Namespace,
    diagnostic: SubclauseDiagnostic,
    issue: int,
    in_progress: list[str],
    workdir: Path,
) -> dict:
    """Run a single pass: write diagnostic → inner orch → cycle dispatch."""
    diag_path = write_diagnostic(workdir, diagnostic)
    result = invoke_inner_orchestrator(
        args, diag_path, issue, in_progress,
    )
    if result.get("status") != "cycle":
        return {"status": "satisfied"}
    members = result.get("members", [])
    if args.subclause in members and in_progress:
        return result
    dispatch_cycle(args, members, workdir)
    return {"status": "satisfied"}


def main(argv=None) -> None:
    """Run the outer orchestrator pipeline."""
    args = parse_args(argv)
    in_progress = parse_in_progress(args.in_progress)
    print(
        f"Outer orchestrator: §{args.subclause}, model {args.model},"
        f" in-progress {in_progress}",
        file=sys.stderr,
    )

    diagnostic = invoke_oracle(
        args.subclause, str(args.lrm), model=args.model,
    )
    if diagnostic.verdict == "yes":
        print(f"§{args.subclause} already satisfied; nothing to do.",
              file=sys.stderr)
        emit_status({"status": "satisfied"})
        return

    issue = find_or_create_issue(args.subclause)

    with tempfile.TemporaryDirectory() as tmp:
        workdir = Path(tmp)
        in_progress_extended = in_progress + [args.subclause]

        for attempt in range(_MAX_RETRIES + 1):
            result = run_pipeline_pass(
                args, diagnostic, issue, in_progress_extended, workdir,
            )
            if result.get("status") == "cycle":
                emit_status(result)
                return
            diagnostic = invoke_oracle(
                args.subclause, str(args.lrm), model=args.model,
            )
            if diagnostic.verdict == "yes":
                emit_status({"status": "satisfied"})
                return
            if attempt < _MAX_RETRIES:
                print(
                    f"Pass {attempt + 1} did not converge for"
                    f" §{args.subclause}; retrying once with the fresh"
                    " diagnostic.",
                    file=sys.stderr,
                )

    label_issue_pipeline_stuck(issue, diagnostic)
    emit_status({"status": "stuck", "issue": issue})
    sys.exit(1)
