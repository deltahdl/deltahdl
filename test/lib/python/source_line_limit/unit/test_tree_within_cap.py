"""The tree this repository holds must stay inside the cap its gate enforces.

The gate that counts lines stands in front of the build, so a file over the cap
holds back every tier behind it and the run that reports the breach reports
nothing else. That is what the gate is for, and it is also why the breach is
worth stating a second time, from a workflow that stands on its own terms: a
tree that has grown a file too long then says which file in a run that is green
apart from it.

The cap is not written here. It is read from the step that enforces it, so the
two cannot be changed apart and only one of them is ever the limit.
"""

from pathlib import Path

from lib.python import source_line_limit

REPO_ROOT = Path(__file__).resolve().parents[5]
GATE = REPO_ROOT / ".github" / "workflows" / "deltahdl.yml"
JOB = "static-analysis"

SUFFIXES = (".cpp", ".h")
ROOTS = (REPO_ROOT / "src", REPO_ROOT / "test" / "src")


def caps() -> list[int]:
    """Read every file-length cap the gate's scanning job enforces."""
    jobs = source_line_limit.steps_of(GATE.read_text(encoding="utf-8"))
    return source_line_limit.line_caps(jobs[JOB])


def test_the_gate_states_one_length_cap_for_the_scan_to_mirror() -> None:
    """Two caps, or none, leave nothing for a second reading to check."""
    assert len(caps()) == 1


def test_no_source_file_is_longer_than_the_cap_the_gate_enforces() -> None:
    """A file over the cap holds back every tier, so it is named here too."""
    assert not source_line_limit.over_limit(ROOTS, caps()[0], SUFFIXES)
