"""Shared data structures for the satisfaction pipeline.

Defines the in-memory contract shared by the satisfaction-pipeline scripts
introduced in #1265 and seeded by #1266:

  - The five-part satisfaction predicate (a)-(e), exposed as
    ``SATISFACTION_CONDITIONS``.
  - The ``is_subclause_satisfied`` diagnostic shape, exposed as
    ``SubclauseDiagnostic``: per-condition ``ConditionStatus`` plus a
    derived roll-up ``Verdict``.
  - The ``compute_subclause_dependencies`` return shape, exposed as
    ``SubclauseDependencies``: an ordered list of subclause identifiers.
"""

from dataclasses import dataclass
from typing import Literal, TypeAlias


SATISFACTION_CONDITIONS: tuple[str, ...] = (
    "rule_coverage",
    "test_coverage",
    "test_placement",
    "naming",
    "deduplication",
)


SATISFIED: Literal["satisfied"] = "satisfied"


ConditionStatus: TypeAlias = Literal["satisfied"] | list[str]
Verdict: TypeAlias = Literal["yes", "no"]
SubclauseDependencies: TypeAlias = list[str]


@dataclass(frozen=True)
class SubclauseDiagnostic:
    """Structured diagnostic returned by ``is_subclause_satisfied``.

    Each of the five satisfaction conditions is either ``SATISFIED`` (the
    condition is met) or a non-empty list of concrete failure descriptions
    (the condition is not met).  The ``verdict`` property is ``"yes"`` iff
    every condition is satisfied, else ``"no"``.
    """

    rule_coverage: ConditionStatus
    test_coverage: ConditionStatus
    test_placement: ConditionStatus
    naming: ConditionStatus
    deduplication: ConditionStatus

    @property
    def verdict(self) -> Verdict:
        """``"yes"`` iff every condition is satisfied, else ``"no"``."""
        for condition in SATISFACTION_CONDITIONS:
            if getattr(self, condition) != SATISFIED:
                return "no"
        return "yes"
