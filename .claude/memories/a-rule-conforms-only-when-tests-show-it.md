---
name: a-rule-conforms-only-when-tests-show-it
description: "When a clause is checked against deltahdl, a case of a rule conforms only when a test in the tree exercises that case and asserts the standard's outcome; reading src/ never settles it, and an untested case is filed on its rule's issue; the tests and the open issues are the only record of conformance."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 86699205-8167-4d43-95d1-668dd7cf1a13
  modified: 2026-10-28T16:23:00.968Z
---

# A rule conforms only when tests show it

When a clause of a standard is checked against deltahdl, whether in a reconciliation, a recheck or a survey of one subclause, every case of every rule in it is looked up in `test/`. A case conforms only when a test exercises that exact case and asserts the outcome the standard gives. CI runs every test on every push, so a test on a green `main` is a run showing the case holds. A case with no such test is a finding, filed on its rule's issue per [[one-indivisible-problem-per-issue]], whatever reading `src/` suggests about it.

**Why:** Reading code predicts how it behaves, and the prediction fails often enough that a verdict reached by reading cannot be trusted to have found every fault: a path that looks right fails on an input nobody traced, and a fault behind an earlier failure stays out of sight. A test is evidence that CI checks again on every push. A list of untested cases also says exactly what is left, where a verdict from reading says nothing about what was skipped.

The tests are the record of what deltahdl meets, and the open issues are the record of what it does not yet meet. No third record of conformance, such as a file mapping rules to tests, is kept beside them.

**Why:** Tests written first under test-driven development already name every case deltahdl handles, and CI checks them on every push; a parallel record would repeat them and drift from them. What tests cannot show is a rule nobody has written a test for, and that is found by reading the standard, a section at a time through its Reconcile issue (see the autopilot skill), and filed as the rule's issue.

**How to apply:** List each rule's cases as in [[fixing-a-rule-in-full]]. For each case, search `test/src/unit/` for a test of it in three ways: by the subclause in the file name, by the `Subclause("…")` a report test names, and by the construct's own source text, since the test may sit under a neighbouring clause ([[searching-for-an-existing-report-before-filing]]). Record the test that covers each case, or file the case as untested. This is how a check reaches its verdict without a local build or probe ([[verifying-through-ci]]).
