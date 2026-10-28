---
name: fixing-a-rule-in-full
description: "An issue of a standard is fixed for every case of its rule (each allowed and forbidden form, in every place it can be written, with every operand or type it names), a test per case, in one commit; never only for the example the issue gives."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 86699205-8167-4d43-95d1-668dd7cf1a13
  modified: 2026-10-28T14:38:01.125Z
---

# Fixing a rule in full

A fix reaches the whole rule an issue documents, not only the example the issue gives. Before writing it, list every case of the rule:

- each form the rule allows and each form it forbids;
- each written in every place the standard lets that form appear: a module, interface, program, checker, package, class, generate block, task or function, or the compilation unit, as applies;
- each with every kind of operand or type the rule names.

Write a test for each case and make deltahdl pass all of them in the same commit.

**Why:** A fix shaped to one example leaves the rule's other forms as broken as they were. Each is met later by whichever session trips over it and filed as an issue of its own, so one fault in deltahdl surfaces as a chain of issues, each paying for a CI run of its own. Listing the cases first settles the rule in one push. A forbidden form needs its nearest allowed form tested beside it because a check written for the forbidden form tends to catch the legal form next to it too, and then reports an error on valid code.

**How to apply:**

- Draw the list from the clause itself, per [[lrm-source-of-truth]]; the cases the issue names are a start, not the whole.
- For each forbidden form, write one test that it is reported, per [[naming-the-report-in-a-rejection-test]], and one that the nearest allowed form is accepted without a report.
- Add a case found while fixing to the fix, never to a new issue ([[solving-what-a-session-finds]]).
- Choose inputs that tell correct code from incorrect ([[discriminating-test-inputs]]).
- Push the tests with the fix and let the run say which pass ([[verifying-through-ci]]).
- An issue about deltahdl itself, such as a coverage gap, has no rule behind it; fix the problem it names.
