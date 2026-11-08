---
name: clang-format-style-flag
description: "Run clang-format -i --style=google on every touched file, from the LLVM major install-llvm defaults to; the style flag is required and the tool may be run locally."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 71fdefb1-3397-48b8-838f-7c5e17be7223
  modified: 2026-11-08T03:24:30.634Z
---

# Formatting with clang-format

Always run `clang-format -i --style=google` on every file a change touches.

**Why:** This is the one tool the repository allows to be run locally over what CI would otherwise judge, and the reason is the `-i`: it rewrites the file, so running it is how the committed bytes come to exist. Every other gate only judges what is already there, and judging belongs to CI — see [verifying-through-ci](verifying-through-ci.md). The style flag matters because the repository has no `.clang-format` file, so a bare `clang-format -i` falls back to LLVM style and reformats the entire file, splitting `if`/`return` and changing switch indentation. That produces a large spurious diff which buries the real change and fails the gate. CI checks with `clang-format --dry-run --Werror --style=google`.

**The major CI runs:** Run the `clang-format` of the LLVM major the `major` input of `.github/actions/install-llvm/action.yml` defaults to, as `$(brew --prefix llvm@<major>)/bin/clang-format`. The bare `clang-format` on the PATH is Homebrew's newest LLVM, and a newer major lays out some code differently: LLVM 23 moved the closing `};` of a braced initializer that begins on its own line, and LLVM 22, which the `clang-format` job runs, refused that layout. A change formatted with the wrong major fails that job on a line the change never meant to touch.

**How to apply:** Pass the style flag every time, to the binary of the major CI installs. If it is missed, `git checkout` the files, re-apply the edits, and re-format with the flag. Do not then run the `--dry-run --Werror` form to confirm: that is the judging half, it is a CI job, and `-i` has already written whatever it would report. The formatting gate runs across all of `src/` and `test/`, so it stays red on pre-existing violations regardless of the change in hand.
