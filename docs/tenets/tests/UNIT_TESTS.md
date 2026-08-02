# Unit Test Tenets

These are the non-negotiable rules for unit tests. A tenet is true whatever this repository holds: it names no language, no tool, no directory and no count. Where a tenet and the repository disagree, the repository is what changes.

## Table of Contents

- [Inputs Must Be Able to Fail](#inputs-must-be-able-to-fail)
- [Coverage Counts Visits, Not Variety](#coverage-counts-visits-not-variety)

## Inputs Must Be Able to Fail

Choose every input so that incorrect code would produce a different result from correct code.

Some values make two distinct quantities coincide. At zero, an offset and a count are the same number. At one, a product and a sum are. For an empty collection, the first element and the last are. Where a range begins where the counting begins, a position and the name of that position are. At each such value, code that confuses the two quantities returns the right answer anyway, so a test built on it passes whether the behaviour is implemented or not. It asserts nothing about the rule it names, however precisely the name states the rule.

Pick a value where the quantities differ. When a rule says that one thing determines another, vary the determining thing from test to test. If every test supplies its most ordinary form, the rule is untested no matter how many tests there are, and adding more tests in the same shape cannot find the defect.

Look hardest where the ordinary form is also the convenient one. Every author independently reaches for the convenient value, so the whole suite comes to rest on the single input that cannot distinguish anything. A suite in that state is not weakly tested in places. It is silent about one rule everywhere at once.

## Coverage Counts Visits, Not Variety

A line reported as covered is a line that ran, and nothing more.

Total branch coverage is necessary and it is not sufficient. Coverage asks whether control reached a place. It never asks whether control arrived carrying a value that could tell right from wrong. Code exercised only by inputs that cannot fail is reported as covered and reported as tested, and it is neither.

So do not take a coverage requirement met in full as evidence that a rule holds. It is evidence that the lines implementing the rule are reachable. When the number is the only thing standing behind a behaviour, the behaviour is unverified.
