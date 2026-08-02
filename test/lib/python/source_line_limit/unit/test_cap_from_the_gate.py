"""Tests for the reading that takes a cap out of the step enforcing it.

A workflow declares more than one job and a job more than one step, so the
fixtures below hold a job with no steps at all and a scan whose counting step
sits behind two that count nothing. The step that compares a number without
counting one is the input that separates a cap from any other limit a script
happens to enforce: a reading that took whichever number it found first would
report it as the file-length cap.
"""

from lib.python.source_line_limit import Step, line_caps, steps_of

CHECKOUT: Step = {"uses": "actions/checkout@v5"}
FORMATTING: Step = {"name": "check formatting", "run": "clang-format --dry-run"}
COUNTING: Step = {
    "name": "check file line limits",
    "run": (
        'lines=$(wc -l < "$f")\n'
        'if [ "$lines" -gt 1000 ]; then\n'
        '  echo "::error file=$f,line=1001::$f has $lines lines"\n'
        "fi\n"
    ),
}
COUNTING_ELSEWHERE: Step = {
    "name": "check test file line limits",
    "run": (
        'lines=$(wc -l < "$t")\n'
        'if [ "$lines" -gt 500 ]; then\n'
        '  echo "::error file=$t,line=501::$t has $lines lines"\n'
        "fi\n"
    ),
}
COMPARING: Step = {
    "name": "check the shard count",
    "run": 'if [ "$shards" -gt 4 ]; then exit 1; fi\n',
}

WORKFLOW = """
jobs:
  static-analysis:
    runs-on: ubuntu-24.04
    steps:
      - name: check formatting
        run: clang-format --dry-run
      - uses: actions/checkout@v5
  ending:
    runs-on: ubuntu-24.04
"""


def test_steps_of_carries_every_job_the_workflow_declares() -> None:
    """A workflow's jobs all reach the reading, whatever they hold."""
    assert sorted(steps_of(WORKFLOW)) == ["ending", "static-analysis"]


def test_steps_of_carries_the_steps_of_a_job_in_the_order_written() -> None:
    """A job's steps arrive as written rather than in any order of their own."""
    assert steps_of(WORKFLOW)["static-analysis"] == [FORMATTING, CHECKOUT]


def test_steps_of_gives_a_job_that_declares_no_steps_an_empty_list() -> None:
    """A job with nothing to run holds no steps rather than failing to read."""
    assert not steps_of(WORKFLOW)["ending"]


def test_the_cap_is_read_from_the_step_that_counts_lines() -> None:
    """The number the counting step compares against is the cap in force."""
    assert line_caps([CHECKOUT, FORMATTING, COUNTING]) == [1000]


def test_a_number_compared_without_counting_lines_is_not_a_cap() -> None:
    """A limit on something other than a length is not the length limit."""
    assert not line_caps([COMPARING])


def test_every_step_that_counts_lines_states_a_cap_of_its_own() -> None:
    """Two counting steps enforce two caps, and the higher is not the only one."""
    assert line_caps([COUNTING, COUNTING_ELSEWHERE]) == [500, 1000]
