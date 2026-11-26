---
name: fixing-a-problem-in-full
description: "Every case of an issue's rule (each allowed and forbidden form, in every place it can be written, with every operand or type it names) is listed before the fix, held by the issue in hand or by the issue of another problem under the rule; the fix reaches every case its issue lists, a test per case, in one push, never only the example the issue gives."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 86699205-8167-4d43-95d1-668dd7cf1a13
  modified: 2026-11-21T02:54:00.439Z
---

# Fixing a problem in full

A fix reaches every case its issue lists, not only the example the issue gives, and an issue holds one problem under a rule ([one-indivisible-problem-per-issue](one-indivisible-problem-per-issue.md)). Before writing the fix, list every case of the rule:

- each form the rule allows and each form it forbids;
- each written in every place the standard lets that form appear: a module, interface, program, checker, package, class, generate block, task or function, or the compilation unit, as applies;
- each with every kind of operand or type the rule names.

See that each case is on the open issue of its problem or is already shown by a passing test. Then write a test for each case the issue in hand lists and make deltahdl pass all of them in the same push.

**Why:** A fix shaped to one example leaves the rule's other forms as broken as they were. Each is met later by whichever session trips over it and filed as an issue of its own, so one fault in deltahdl surfaces as a chain of issues, each paying for a CI run of its own. Listing the cases first, and filing each problem before any is fixed, leaves no case off the record while keeping each fix small. A forbidden form needs its nearest allowed form tested beside it because a check written for the forbidden form tends to catch the legal form next to it too, and then reports an error on valid code.

**How to apply:**

- Draw the list from the clause itself, per [lrm-source-of-truth](lrm-source-of-truth.md); the cases the issue names are a start, not the whole.
- For each forbidden form, write one test that it is reported, per [naming-the-report-in-a-rejection-test](naming-the-report-in-a-rejection-test.md), and one that the nearest allowed form is accepted without a report.
- A case's test may already be in the tree with `DISABLED_` in front of its name, per [lrm-tests-issues-are-tests-only](lrm-tests-issues-are-tests-only.md). Trace through the code why it fails, then remove the prefix in the commit that makes it pass.
- A case found while fixing joins the fix when the fix in hand corrects it, and otherwise goes on the issue of its problem ([a-finding-joins-the-push-or-is-filed](a-finding-joins-the-push-or-is-filed.md)).
- Choose inputs that tell correct code from incorrect ([discriminating-test-inputs](discriminating-test-inputs.md)).
- Write each test before the fix and trace through the code why it fails because of the rule in hand, building nothing locally ([test-driven-development](test-driven-development.md)). A test that fails for another reason has found another problem, which is dealt with as [a-finding-joins-the-push-or-is-filed](a-finding-joins-the-push-or-is-filed.md) says before the fix is designed. Never bend the tests around it unrecorded.
- Push the tests with the fix and let the CI run give the verdict over all of deltahdl ([verifying-through-ci](verifying-through-ci.md)).
- An issue about deltahdl itself, such as a coverage gap, has no rule behind it; fix the problem it names.
