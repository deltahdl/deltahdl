---
name: clang-format-style-flag
description: Run clang-format -i --style=google on every touched file; the style flag is required.
metadata:
  type: feedback
---

# Formatting with clang-format

Always run `clang-format -i --style=google` on every file a change touches.

**Why:** The style flag matters because the repository has no `.clang-format` file, so a bare `clang-format -i` falls back to LLVM style and reformats the entire file, splitting `if`/`return` and changing switch indentation. That produces a large spurious diff which buries the real change and fails the gate. CI checks with `clang-format --dry-run --Werror --style=google`.

**How to apply:** Pass the style flag every time. If it is missed, `git checkout` the files, re-apply the edits, and re-format with the flag. The `--dry-run --Werror` form afterwards adds nothing, since `-i` has already written whatever it would report. The formatting gate runs across all of `src/` and `test/`, so it stays red on pre-existing violations regardless of the change in hand.
