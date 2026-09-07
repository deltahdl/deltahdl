---
name: discriminating-test-inputs
description: Choose every test input so that incorrect code would give a different answer from correct code.
metadata:
  type: feedback
---

# Choosing an input that discriminates

Choose every input so that incorrect code would give a different answer from correct code.

**Why:** Some values make two quantities coincide — an offset and a count at zero, or an index and a storage offset in a vector declared `[N:0]` — and a test built on one passes whether the behaviour exists or not. Such a test is indistinguishable from a real one in the log, so it does not fail when the feature is removed.

**How to apply:** Before settling on a literal, ask what the code would return if the behaviour under test were missing. If the answer is the same value, move the input off the coincidence: use a non-zero offset, an index that differs from its storage offset, a width that is not the default. The same discipline applies to what the test asserts, per [naming-the-report-in-a-rejection-test](naming-the-report-in-a-rejection-test.md).
