---
name: lrm-tests-issues-are-tests-only
description: "An issue labelled lrm-tests is worked with tests alone, nothing under src/, failing tests under DISABLED_; every other issue lands its fix and its tests together in one commit."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 5dbdb501-d495-4164-9f4a-bd5e7f9f1fb3
  modified: 2026-11-21T17:24:06.607Z
---

# lrm-tests issues are tests only

An issue labelled `lrm-tests` asks for a test of every case of every rule in one section of a standard, and for nothing else. Its commit changes nothing under `src/`, however small the fix a failing test points to. Every test it asks for lands in the one push that closes it, never spread over several pushes. A test deltahdl passes carries its plain name. A test deltahdl fails carries `DISABLED_` in front of its name, as in `TEST(Suite, DISABLED_Name)`: GoogleTest builds such a test but leaves it out of a run unless asked, so it neither passes nor fails. The commit that later makes it pass removes the prefix.

Every other issue is fair game for a fix: its commit delivers the src change and every case's test together, each passing under its plain name, and no src line lands uncovered ([test-driven-development](test-driven-development.md), [fixing-a-problem-in-full](fixing-a-problem-in-full.md)). Its tests are never pushed ahead of the fix, disabled or not.

**Why:** an `lrm-tests` issue exists so that every case has a test in `test/`, not only a sentence in an issue, with the prefixed tests marking exactly what is left. Keeping it to tests keeps that inventory separate from the fixes, which belong to the rule issues. A rule issue, by contrast, is finished only when the rule works, so its tests and its fix travel together.

**How to apply:**

- For an `lrm-tests` issue, trace each new test through the code under its plain name, building nothing locally ([verifying-through-ci](verifying-through-ci.md)), and judge whether deltahdl passes it. A test that passes keeps its plain name. A test that fails because deltahdl does not do what its case states takes the prefix. A test failing for another reason is wrong and is corrected, or has found a defect of another rule, which becomes a case of that rule's issue with a test of its own ([a-finding-joins-the-push-or-is-filed](a-finding-joins-the-push-or-is-filed.md)).
- The `lrm-tests` push also closes each rule issue all of whose cases now pass under their plain names ([a-push-closes-an-issue](a-push-closes-an-issue.md)): that records conformance found, not a fix.
- Choose a name no other test has once the prefix is gone.
- A test carrying the prefix shows nothing about its case. The case stays unticked in its rule's issue, with the test named beside it ([a-rule-conforms-only-when-tests-show-it](a-rule-conforms-only-when-tests-show-it.md)).
- A test CI shows failing under its plain name takes the prefix in a push of its own, per [fixing-a-red-run](fixing-a-red-run.md).
- On CI, a test carrying the prefix runs when its binary is passed `--gtest_also_run_disabled_tests --gtest_filter=Suite.DISABLED_Name` to its binary.
- The fix of a rule removes the prefix from every test of the rule, and closes its issue only when none of its cases' tests still carries one.
- A test that cannot compile because it needs a declaration deltahdl lacks waits for its fix, its case naming the declaration.
