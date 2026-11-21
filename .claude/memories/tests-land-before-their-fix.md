---
name: tests-land-before-their-fix
description: "Only an issue that asks for tests ahead of the functionality (labelled lrm-tests) lands tests without their fix, failing ones under DISABLED_; an issue asking to solve a rule lands its tests and its fix in one commit."
metadata:
  node_type: memory
  type: feedback
  originSessionId: b425c181-0dc9-4105-9628-ad8462acdd57
  modified: 2026-11-21T02:13:31.402Z
---

# Tests land before their fix

This holds only for an issue that asks for tests before deltahdl has the functionality they test: an issue labelled `lrm-tests`, which asks for the tests of one section of a standard ahead of any fix and changes nothing under `src/`. The `bylabel` form of the autopilot skill works through such issues. For one of them, a unit test under `test/src/unit/` is committed and pushed once it is written and has been run, whether or not deltahdl passes it. A test deltahdl passes carries its plain name. A test deltahdl fails carries `DISABLED_` in front of its name, as in `TEST(Suite, DISABLED_Name)`: GoogleTest builds a test so named and leaves it out of a run unless asked for it, so it neither passes nor fails. The commit that later makes deltahdl pass the test removes the prefix.

An issue that asks to solve a rule is different: its commit delivers the functionality and every case's test together, each test passing under its plain name, and closes the issue ([a-commit-closes-an-issue](a-commit-closes-an-issue.md), [fixing-a-rule-in-full](fixing-a-rule-in-full.md)). Its tests are still written and run before the fix and seen to fail ([test-driven-development](test-driven-development.md)), but they are not pushed disabled ahead of it.

**Why:** An `lrm-tests` issue exists so that every case deltahdl does not yet meet has a test in `test/`, not only a sentence in an issue: the tests carrying the prefix are then the whole of what is left, and a test failing under its plain name is something that worked and stopped working, never lost among expected failures. A rule's issue, by contrast, is finished only when the rule works, so landing its tests without the fix would leave the rule half done on `main`.

**How to apply:**

- For an `lrm-tests` issue, build and run each new test under its plain name first, and read why it fails. A test that passes keeps its plain name. A test that fails because deltahdl does not do what its case states takes the prefix. A test that fails for another reason is wrong and is corrected, or has found a defect of another rule, which becomes a case of that rule's issue with a test of its own ([what-does-not-get-filed](what-does-not-get-filed.md)).
- Choose a name no other test has once the prefix is gone ([unique-test-names](unique-test-names.md)).
- A test that carries the prefix shows nothing about its case. The case stays unticked in its rule's issue, with the test named beside it ([a-rule-conforms-only-when-tests-show-it](a-rule-conforms-only-when-tests-show-it.md)).
- To run a test that carries the prefix, pass `--gtest_also_run_disabled_tests --gtest_filter=Suite.DISABLED_Name` to its binary.
- The fix of a rule removes the prefix from every test of the rule and closes its issue only when no test of its cases still carries one.
- A test that cannot compile against deltahdl as it stands, because it needs a declaration deltahdl lacks, waits for its fix, and its case says which declaration.
