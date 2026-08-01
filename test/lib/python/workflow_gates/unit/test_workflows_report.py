"""The workflows this repository runs must not hide their own scanning steps.

Two claims are made here. The first holds of every job in every workflow and
names nothing: a step between two that report regardless is one the reporting
hides. The second needs the jobs whose scanning has to reach their last step to
be named, because no reading of a workflow can tell such a job from one that
ends in an epilogue -- so GATES names them, and a lint job added to a workflow
later has to be added there too.
"""

from collections.abc import Callable
from pathlib import Path

from lib.python import workflow_gates

REPO_ROOT = Path(__file__).resolve().parents[5]
WORKFLOWS_DIR = REPO_ROOT / ".github" / "workflows"
WORKFLOWS = sorted(WORKFLOWS_DIR.glob("*.yml"))

# The jobs that read the whole tree rather than the change, and so are the ones
# capable of holding a backlog behind a breach that stands.
GATES = {
    "deltahdl.yml": ("static-analysis",),
    "documentation.yml": ("jsonlint", "markdownlint", "yamllint"),
    "scripts.yml": ("static-analysis",),
}

Steps = list[workflow_gates.Step]
Report = Callable[[Steps], list[str]]


def text_of(path: Path) -> str:
    """Read the workflow file at *path*."""
    return path.read_text(encoding="utf-8")


def jobs_in(path: Path) -> dict[str, Steps]:
    """Read the jobs of the workflow file at *path*."""
    return workflow_gates.jobs_of(text_of(path))


def answered_by_the_run() -> dict[str, list[str]]:
    """Map each workflow to the jobs an unrelated failure can silence."""
    found: dict[str, list[str]] = {}
    for path in WORKFLOWS:
        named = workflow_gates.jobs_testing_the_run(text_of(path))
        if named:
            found[path.name] = named
    return found


def breaches(report: Report) -> dict[str, dict[str, list[str]]]:
    """Collect what *report* names, by workflow file and by job within it."""
    found: dict[str, dict[str, list[str]]] = {}
    for path in WORKFLOWS:
        named = {
            job: names
            for job, steps in jobs_in(path).items()
            if (names := report(steps))
        }
        if named:
            found[path.name] = named
    return found


def gates_that_are_not(holds: Callable[[Steps], bool]) -> list[str]:
    """Name every gate in GATES that *holds* rejects, or that is not there."""
    failing: list[str] = []
    for filename, jobs in GATES.items():
        declared = jobs_in(WORKFLOWS_DIR / filename)
        for job in jobs:
            steps = declared.get(job)
            if steps is None or not holds(steps):
                failing.append(f"{filename}:{job}")
    return failing


def test_every_named_gate_reports_through_its_own_last_step() -> None:
    """A gate whose scanning stops short of its end is not a gate."""
    assert not gates_that_are_not(workflow_gates.reports_to_the_end)


def test_no_workflow_job_hides_a_step_that_reports_findings() -> None:
    """Between two steps that report regardless, every step reports too."""
    assert not breaches(workflow_gates.hidden_steps)


def test_no_reporting_step_leaves_the_job_green_on_its_own_findings() -> None:
    """Reporting is not un-gating: a breach a step names still fails the job."""
    assert not breaches(workflow_gates.ungated_steps)


def test_no_job_is_held_back_by_a_failure_it_has_no_relation_to() -> None:
    """A job asks after the jobs it needs, never after the run as a whole."""
    assert not answered_by_the_run()
