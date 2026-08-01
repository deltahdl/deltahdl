"""Tests for the reading that finds a job's hidden steps.

The jobs below put the reporting region in the middle of the step list and the
breach in the middle of the region, so a reading that took the whole job for
the region, or that named every unconditional step rather than the ones inside
it, gives a different answer from the one these tests expect.
"""

from lib.python.workflow_gates import (
    Step,
    conditions_of,
    hidden_steps,
    jobs_of,
    jobs_testing_the_run,
    name_of,
    reporting_region,
    reports_to_the_end,
    runs_regardless,
    tests_the_run,
    ungated_steps,
)

CHECKOUT: Step = {"uses": "actions/checkout@v5"}
INSTALL: Step = {"name": "install the tools", "run": "pip install pmd"}
CACHED: Step = {
    "continue-on-error": True,
    "name": "restore the cache",
    "uses": "actions/cache@v5",
}
FORMATTING: Step = {
    "if": "${{ !cancelled() }}",
    "name": "check formatting",
    "run": "clang-format --dry-run",
}
LINE_LIMITS: Step = {"name": "check file line limits", "run": "wc -l"}
COPY_PASTE: Step = {
    "if": "${{ always() }}",
    "name": "detect copy-paste",
    "run": "pmd cpd",
}
ADVISORY: Step = {
    "continue-on-error": True,
    "if": "${{ !cancelled() }}",
    "name": "count what is left to do",
    "run": "grep -c TODO",
}
WHEN_CHANGED: Step = {
    "if": "${{ steps.detect.outputs.changed == 'true' }}",
    "name": "lint YAML",
    "run": "yamllint",
}
UNTITLED: Step = {"run": "true"}
UPLOAD: Step = {
    "name": "upload what the run produced",
    "uses": "actions/upload-artifact@v4",
}

HIDING = [CHECKOUT, INSTALL, FORMATTING, LINE_LIMITS, COPY_PASTE]
REPORTING = [CHECKOUT, INSTALL, FORMATTING, COPY_PASTE]
NOTHING_REPORTS = [CHECKOUT, INSTALL, WHEN_CHANGED]
ADVISING = [CHECKOUT, INSTALL, FORMATTING, ADVISORY, COPY_PASTE]
TOLERANT_SETUP = [CHECKOUT, CACHED, FORMATTING, COPY_PASTE]
ENDING_IN_AN_EPILOGUE = [CHECKOUT, INSTALL, FORMATTING, COPY_PASTE, UPLOAD]

SCANS: Step = {"name": "check formatting", "run": "clang-format --dry-run"}
WORKFLOW = """
jobs:
  static-analysis:
    runs-on: ubuntu-24.04
    steps:
      - name: check formatting
        run: clang-format --dry-run
      - name: check file line limits
        run: wc -l
  ending:
    runs-on: ubuntu-24.04
"""

# Three jobs in a chain, the middle one guarded by the health of the run and the
# last by the job it needs. The last is the input that tells the two apart: its
# condition holds the word `success` and does not call the function, so a
# reading matching the word alone would name it too.
CONDITIONED = """
jobs:
  build:
    runs-on: ubuntu-24.04
  integration:
    if: ${{ !failure() && !cancelled() }}
    needs: build
    runs-on: ubuntu-24.04
  e2e:
    if: ${{ !cancelled() && needs.integration.result == 'success' }}
    needs: integration
    runs-on: ubuntu-24.04
"""


def test_jobs_of_carries_every_job_the_workflow_declares() -> None:
    """A workflow's jobs all reach the reading, whatever they hold."""
    assert sorted(jobs_of(WORKFLOW)) == ["ending", "static-analysis"]


def test_jobs_of_carries_the_steps_of_a_job_in_the_order_written() -> None:
    """A job's steps arrive as written, since the order is what hides them."""
    assert jobs_of(WORKFLOW)["static-analysis"] == [SCANS, LINE_LIMITS]


def test_jobs_of_gives_a_job_that_declares_no_steps_an_empty_list() -> None:
    """A job with nothing to run holds no steps rather than failing to read."""
    assert not jobs_of(WORKFLOW)["ending"]


def test_name_of_a_step_is_the_name_it_declares() -> None:
    """A named step is called by its name."""
    assert name_of(LINE_LIMITS) == "check file line limits"


def test_name_of_a_step_with_no_name_is_the_action_it_uses() -> None:
    """An unnamed step that uses an action is called by that action."""
    assert name_of(CHECKOUT) == "actions/checkout@v5"


def test_name_of_a_step_with_neither_name_nor_action_says_so() -> None:
    """A step a run list would leave unlabelled is reported as unnamed."""
    assert name_of(UNTITLED) == "<unnamed>"


def test_a_step_conditioned_on_not_cancelled_runs_regardless() -> None:
    """`!cancelled()` holds however the steps ahead of it ended."""
    assert runs_regardless(FORMATTING)


def test_a_step_conditioned_on_always_runs_regardless() -> None:
    """`always()` holds however the steps ahead of it ended."""
    assert runs_regardless(COPY_PASTE)


def test_a_step_conditioned_on_a_finding_does_not_run_regardless() -> None:
    """A condition naming neither form leaves the step behind its neighbours."""
    assert runs_regardless(WHEN_CHANGED) is False


def test_a_step_with_no_condition_does_not_run_regardless() -> None:
    """The default condition stops the step when anything ahead failed."""
    assert runs_regardless(INSTALL) is False


def test_the_region_runs_from_the_first_reporting_step_to_the_last() -> None:
    """Setup ahead of the first reporting step stays out of the region."""
    assert reporting_region(HIDING) == [FORMATTING, LINE_LIMITS, COPY_PASTE]


def test_the_region_ends_at_the_last_step_that_reports() -> None:
    """An epilogue behind the region had nothing hiding it to begin with."""
    assert reporting_region(ENDING_IN_AN_EPILOGUE) == [FORMATTING, COPY_PASTE]


def test_a_job_where_no_step_reports_regardless_has_no_region() -> None:
    """A job that reports only its first breach has nothing in its region."""
    assert not reporting_region(NOTHING_REPORTS)


def test_a_job_whose_last_step_reports_regardless_reports_to_its_end() -> None:
    """A job whose scanning has to reach its end says so on its last step."""
    assert reports_to_the_end(HIDING)


def test_a_job_ending_in_an_epilogue_does_not_report_to_its_end() -> None:
    """A step collected whatever happened is not a scan of the whole tree."""
    assert reports_to_the_end(ENDING_IN_AN_EPILOGUE) is False


def test_a_job_with_no_steps_does_not_report_to_its_end() -> None:
    """There is no last step to read, which is an answer rather than a fault."""
    assert reports_to_the_end([]) is False


def test_a_region_step_with_no_condition_is_hidden() -> None:
    """A scan between two reporting scans is the one the region hides."""
    assert hidden_steps(HIDING) == ["check file line limits"]


def test_a_region_whose_steps_all_report_hides_none_of_them() -> None:
    """Every step in the region reporting is the state being asked for."""
    assert not hidden_steps(REPORTING)


def test_a_step_behind_the_region_is_not_hidden_by_it() -> None:
    """Nothing in the region was standing in the epilogue's way."""
    assert not hidden_steps(ENDING_IN_AN_EPILOGUE)


def test_a_region_step_that_continues_on_error_is_ungated() -> None:
    """A reporting step the job survives states a finding it does not hold."""
    assert ungated_steps(ADVISING) == ["count what is left to do"]


def test_a_setup_step_that_continues_on_error_is_not_ungated() -> None:
    """Ahead of the region there is no finding to gate on, so none is lost."""
    assert not ungated_steps(TOLERANT_SETUP)


def test_conditions_of_carries_the_condition_a_job_declares() -> None:
    """A job's condition arrives as written, since its wording is the subject."""
    assert conditions_of(CONDITIONED)["e2e"] == (
        "${{ !cancelled() && needs.integration.result == 'success' }}"
    )


def test_conditions_of_gives_a_job_declaring_none_an_empty_condition() -> None:
    """A job with no condition carries the default, which names nothing."""
    assert not conditions_of(CONDITIONED)["build"]


def test_a_condition_calling_failure_tests_the_run() -> None:
    """`failure()` is true of any job in the run, related or not."""
    assert tests_the_run(conditions_of(CONDITIONED)["integration"])


def test_a_condition_calling_success_tests_the_run() -> None:
    """`success()` is the same question asked the other way round."""
    assert tests_the_run("${{ success() }}")


def test_a_condition_asking_after_its_needs_does_not_test_the_run() -> None:
    """Comparing a need's result against 'success' calls no status function."""
    assert tests_the_run(conditions_of(CONDITIONED)["e2e"]) is False


def test_a_job_with_no_condition_does_not_test_the_run() -> None:
    """The default condition is about this job's needs and nothing else."""
    assert tests_the_run("") is False


def test_only_the_job_guarded_by_the_run_is_named() -> None:
    """Neither the job with no condition nor the one asking after its needs."""
    assert jobs_testing_the_run(CONDITIONED) == ["integration"]
