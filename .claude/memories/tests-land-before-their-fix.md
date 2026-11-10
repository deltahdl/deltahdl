---
name: tests-land-before-their-fix
description: "A C++ unit test is pushed once it is written, ahead of its fix: under its plain name when deltahdl passes it, and with DISABLED_ in front of its name, until the fix removes the prefix, when deltahdl fails it."
metadata:
  node_type: memory
  type: feedback
  originSessionId: b425c181-0dc9-4105-9628-ad8462acdd57
  modified: 2026-11-10T05:46:37.475Z
---

# Tests land before their fix

A unit test under `test/src/unit/` is committed and pushed once it is written and has been run, whether or not deltahdl passes it. A test deltahdl passes carries its plain name. A test deltahdl fails carries `DISABLED_` in front of its name, as in `TEST(Suite, DISABLED_Name)`: GoogleTest builds a test so named and leaves it out of a run unless asked for it, so it neither passes nor fails. The commit that makes deltahdl pass the test removes the prefix.

**Why:** A test that waits for its fix leaves every case deltahdl does not yet meet out of `test/`, recorded only as a sentence in an issue. The tests then show what is done and never what is missing, and the only way to learn what is missing is to read the standard again. With a test in the tree for every case, the tests that carry the prefix are the whole of what is left. The prefix also keeps a waiting test apart from a break: a test that fails under its plain name is something that worked and stopped working, and it is not lost among thousands of failures that were expected.

**How to apply:**

- Build and run each new test under its plain name first, and read why it fails. A test that passes keeps its plain name. A test that fails because deltahdl does not do what its case states takes the prefix. A test that fails for another reason is wrong and is corrected, or has found a defect of another rule, which becomes a case of that rule's issue with a test of its own ([what-does-not-get-filed](what-does-not-get-filed.md)).
- Choose a name no other test has once the prefix is gone ([unique-test-names](unique-test-names.md)).
- A test that carries the prefix shows nothing about its case. The case stays unticked in its rule's issue, with the test named beside it ([a-rule-conforms-only-when-tests-show-it](a-rule-conforms-only-when-tests-show-it.md)).
- To run a test that carries the prefix, pass `--gtest_also_run_disabled_tests --gtest_filter=Suite.DISABLED_Name` to its binary.
- A fix removes the prefix from every test of the rule it closes, and an issue of a rule closes only when no test of its cases still carries one ([fixing-a-rule-in-full](fixing-a-rule-in-full.md)).
- A test that cannot compile against deltahdl as it stands, because it needs a declaration deltahdl lacks, waits for its fix, and its case says which declaration.
- An issue labelled `lrm-tests` asks for the tests of one section of a standard ahead of any fix. It changes nothing under `src/`, and the existing `bylabel` form of the autopilot skill works through such issues.
