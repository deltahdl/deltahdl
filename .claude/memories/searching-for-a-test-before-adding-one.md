---
name: searching-for-a-test-before-adding-one
description: "Before proposing or adding a test, search all of test/ for one that shows the case, open it and trace the code it runs; add only a test that would catch something it does not."
metadata:
  type: feedback
---

# Searching for a test before adding one

Before proposing or adding a test, search the whole of `test/` for one that already shows the case, open it, and trace the code it runs. Add a test only when you can name what it would catch that the existing one would not.

**Why:** The case may be shown under a neighbouring clause, through the same code. A test proposed before that search suggests a gap that is not there, and duplicates one that is kept up elsewhere.

**How to apply:**

- Search by the construct's source text, by its diagnostic's words, by its subclause, and by the function in `src/` that decides the outcome.
- Expect to find one: [every-lrm-rule-has-been-swept](every-lrm-rule-has-been-swept.md). A test found under `DISABLED_` is the case's test.
- Keep a test that only looks like a duplicate: [a-test-that-constrains-a-fix](a-test-that-constrains-a-fix.md), [renaming-rather-than-deleting-a-duplicate-test](renaming-rather-than-deleting-a-duplicate-test.md).
