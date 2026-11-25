---
name: every-lrm-rule-has-been-swept
description: "Every section of IEEE 1800-2023 has been read for its rules and a test written for each case: a plain name passes, DISABLED_ marks what deltahdl does not yet do; start from those tests."
metadata:
  type: project
---

# Every LRM rule has been swept for tests

Every section of IEEE 1800-2023 has been read for the rules it states, and a test written for each case of each rule. The closed issues labelled `lrm-tests` are the sweep, one per section or rule. A case deltahdl meets has a test under its plain name, and a case it does not meet has one whose name begins with `DISABLED_`. A case whose test could not compile for want of a declaration is named as such on its rule's open issue.

**Why:** A session that does not know the sweep was done writes a test the tree already holds, or removes one without seeing that it stands for a case of the standard.

**How to apply:**

- Expect a case's test to be in `test/src/unit/` already, and look for it first ([searching-for-a-test-before-adding-one](searching-for-a-test-before-adding-one.md)).
- A fix starts from the `DISABLED_` tests of its rule and takes the prefix off each one it makes pass ([lrm-tests-issues-are-tests-only](lrm-tests-issues-are-tests-only.md)).
- A test may predate the sweep and assert what the standard does not give. The clause decides ([lrm-source-of-truth](lrm-source-of-truth.md)), and such a test goes as [a-deleted-test-leaves-its-cases-shown](a-deleted-test-leaves-its-cases-shown.md) says.
- A case the sweep left without a test is a finding ([a-rule-conforms-only-when-tests-show-it](a-rule-conforms-only-when-tests-show-it.md)). A difference only deltahdl's own storage makes, such as a value wider than 64 bits, is not a case unless the rule names it.
