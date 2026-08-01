"""Finds the steps of a CI job that a failure ahead of them hides.

A job runs its steps in order and stops at the first one that fails, so a job
holding several scans reports the earliest breach and nothing else. The scans
behind it never run, and a step that did not run is reported neither passed nor
failed -- which reads, afterwards, exactly like a step that found nothing. A
backlog can then accumulate behind one standing failure for as long as it
stands, and whoever takes that failure on cannot see the size of what they are
taking on until they have already cleared part of it.

A step escapes this by declaring a condition that holds however the steps ahead
of it ended. The steps from the first one declaring such a condition to the last
are the job's reporting region: everything between them is there to report
findings of its own. A step inside the region that declares no such condition is
hidden by the region's own failures, and one allowed to continue on error
reports its findings without holding the job to them.

The region is bounded at both ends because a step can run regardless for either
of two reasons. Ahead of the first are the steps that make the scanning possible
at all -- fetching the tree, installing the tools -- which have no findings of
their own and stop everything when they fail, as they should. The last is often
an epilogue -- a disk-space reading, an upload of what the run produced -- which
wanted collecting whatever happened rather than reporting on the tree, and what
follows an epilogue was never being hidden by anything.

That leaves the case of a job whose reporting has to reach its final step, which
no span can tell from a job that ends in an epilogue. Such a job says so by
guarding its last step, and :func:`reports_to_the_end` reads that.

A step that runs and finds something is still not a step anybody is shown. A
runner puts a written line into the log of the step that wrote it, and nothing
else, unless the line is addressed to the run as an annotation -- in which case
it reaches the summary, and the first command anybody runs after pushing. So a
scan whose findings are its own wording has a second way to go unread, and
:func:`plain_reports` reads which of a step's lines take it.

The same hiding happens a level up, between jobs rather than within one. A job
whose condition asks how the *run* went is held back by any failure anywhere,
including in jobs it shares no dependency with, and it is then recorded neither
green nor red -- so a tier can stop reporting for as long as something unrelated
is broken, which is when it is most likely to be drifting. A condition that asks
after the jobs a job needs says the same thing about its own dependencies and
nothing about anybody else's, which is what :func:`asks_after_the_run` reads.
"""

import re
from collections.abc import Callable
from typing import Any

import yaml

Step = dict[str, Any]

# The condition forms that hold whatever the steps ahead of a step did. Both
# stop holding when the run is cancelled, which is the one interruption a
# reporting step has nothing to say about.
RUNS_REGARDLESS = ("always()", "!cancelled()")

UNNAMED = "<unnamed>"

# The status functions whose subject is the whole run rather than the jobs a job
# depends on. `cancelled()` is not one of them: a cancelled run was stopped by
# somebody, which every job has the same reason to respect, whereas whether some
# other job failed is not a fact about this job at all.
RUN_WIDE = ("failure()", "success()")


def _jobs(text: str) -> dict[str, Any]:
    """Return the job of every name the workflow *text* declares."""
    parsed: Any = yaml.safe_load(text)
    return {str(name): job for name, job in parsed["jobs"].items()}


def jobs_of(text: str) -> dict[str, list[Step]]:
    """Return the steps of every job in the workflow *text*, by job name."""
    return {
        name: list(job.get("steps", [])) for name, job in _jobs(text).items()
    }


def conditions_of(text: str) -> dict[str, str]:
    """Return the condition every job declares, by job name."""
    return {name: str(job.get("if", "")) for name, job in _jobs(text).items()}


def asks_after_the_run(condition: str) -> bool:
    """Return whether *condition* asks how the run went, rather than its needs."""
    return any(marker in condition for marker in RUN_WIDE)


def jobs_asking_after_the_run(text: str) -> list[str]:
    """Name the jobs an unrelated failure can hold back and silence."""
    return sorted(
        name
        for name, condition in conditions_of(text).items()
        if asks_after_the_run(condition)
    )


def name_of(step: Step) -> str:
    """Return what a run's step list calls *step*."""
    for key in ("name", "uses"):
        if key in step:
            return str(step[key])
    return UNNAMED


def runs_regardless(step: Step) -> bool:
    """Return whether *step* runs however the steps ahead of it ended."""
    condition = str(step.get("if", ""))
    return any(marker in condition for marker in RUNS_REGARDLESS)


def reporting_region(steps: list[Step]) -> list[Step]:
    """Return the steps from the first that runs regardless to the last one."""
    reporting = [
        index for index, step in enumerate(steps) if runs_regardless(step)
    ]
    if not reporting:
        return []
    return steps[reporting[0]:reporting[-1] + 1]


def reports_to_the_end(steps: list[Step]) -> bool:
    """Return whether the job's own last step runs regardless."""
    return bool(steps) and runs_regardless(steps[-1])


def _named_where(steps: list[Step], holds: Callable[[Step], bool]) -> list[str]:
    """Name the reporting-region steps of *steps* that *holds* accepts."""
    return [
        name_of(step) for step in reporting_region(steps) if holds(step)
    ]


def hidden_steps(steps: list[Step]) -> list[str]:
    """Name the reporting-region steps a failure ahead of them would hide."""
    return _named_where(steps, lambda step: not runs_regardless(step))


def ungated_steps(steps: list[Step]) -> list[str]:
    """Name the reporting-region steps whose findings leave the job green."""
    return _named_where(
        steps, lambda step: bool(step.get("continue-on-error"))
    )


# What a runner reads as a report addressed to the run rather than to the step
# it came from: a written line beginning with these characters. Whatever else a
# step writes lands in a log that only somebody who goes looking for it opens,
# so a finding written any other way is a finding nobody reading the run's own
# summary is shown.
ANNOTATION = "::"

# The words a script writes with. A step reports what it found either through
# one of these, in its own wording, or through the tool it runs, which words
# its findings itself. Only the former is the step's to hold to a form.
WRITERS = ("echo", "printf")

# What sends a written line somewhere other than the log: a redirection or a
# pipe. A line ending up in a file, in a runner variable, or in the next
# command is not a report to anybody. Neither is a line with nothing written on
# it: a bare `echo` spaces a log out and states nothing to be held to a form.
DIVERSIONS = (">", "|")

# A command substitution, which may hold pipes of its own. Those belong to the
# text being written rather than to where the writing goes, so they are removed
# before a line is read for diversions.
_SUBSTITUTION = re.compile(r"\$\([^()]*\)")

# A step enforces a length cap by counting a file's lines and comparing the
# count against a number written into the step. Reading the number there is
# what keeps one statement of the limit: a scan that mirrors the gate from
# somewhere else and carries its own copy stops mirroring it the moment either
# copy is changed alone.
COUNTS_LINES = "wc -l"
_CAP = re.compile(r'-gt\s+"?(\d+)"?')


def _logical_lines(script: str) -> list[str]:
    """Return the lines of *script* with backslash continuations joined."""
    return [line.strip() for line in script.replace("\\\n", " ").splitlines()]


def _outside_substitutions(line: str) -> str:
    """Return *line* with its command substitutions removed."""
    shortened = _SUBSTITUTION.sub("", line)
    while shortened != line:
        line, shortened = shortened, _SUBSTITUTION.sub("", shortened)
    return shortened


def _writes_to_the_log(line: str) -> bool:
    """Return whether *line* writes something the step's log will show."""
    words = line.split(maxsplit=1)
    if len(words) < 2 or words[0] not in WRITERS:
        return False
    remainder = _outside_substitutions(line)
    return not any(mark in remainder for mark in DIVERSIONS)


def _written_by(line: str) -> str:
    """Return the start of what *line* writes, with its quoting removed."""
    return line.split(maxsplit=1)[1].strip().lstrip("\"'")


def plain_reports(step: Step) -> list[str]:
    """Return the lines *step* writes to the log that are not annotations."""
    return [
        line
        for line in _logical_lines(str(step.get("run", "")))
        if _writes_to_the_log(line)
        and not _written_by(line).startswith(ANNOTATION)
    ]


def steps_reporting_plainly(steps: list[Step]) -> list[str]:
    """Name the reporting-region steps whose findings miss the run summary."""
    return _named_where(steps, lambda step: bool(plain_reports(step)))


def line_caps(steps: list[Step]) -> list[int]:
    """Return every file-length cap *steps* enforce by counting lines."""
    found: set[int] = set()
    for step in steps:
        script = str(step.get("run", ""))
        if COUNTS_LINES in script:
            found.update(int(cap) for cap in _CAP.findall(script))
    return sorted(found)
