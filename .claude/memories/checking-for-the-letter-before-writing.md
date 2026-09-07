---
name: checking-for-the-letter-before-writing
description: Run ls test/src/unit/ for the subclause before choosing a letter suffix; an earlier split may already hold it.
metadata:
  type: feedback
---

# Checking for the letter before writing the file

Run `ls test/src/unit/ | grep <subclause>` before choosing a suffix.

**Why:** The name one letter past the end of a family is easy to guess wrong, because an earlier split may already have claimed it, and writing over that file destroys the cases in it. A `>` redirect onto `test_parser_annex_a_09_03a.cpp` destroyed the ten cases commit `c30f5c7ce` had already put there.

**How to apply:** One `ls` before the write. It costs one call, and it is the only thing standing between a split and silently deleted coverage. See [test-file-letter-suffixes](test-file-letter-suffixes.md) for the family the letter belongs to.
