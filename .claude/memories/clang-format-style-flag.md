---
name: clang-format-style-flag
description: "Run clang-format -i --style=google on every touched .cpp and .h file, and on nothing else, from the LLVM major install-llvm defaults to."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 71fdefb1-3397-48b8-838f-7c5e17be7223
  modified: 2026-11-21T02:51:33.406Z
---

# Formatting with clang-format

Run `clang-format -i --style=google` on every `.cpp` and `.h` file a change touches, and on no other file, with the `clang-format` of the LLVM major CI installs.

**Why:**

- **The style flag.** The repository has no `.clang-format` file, so a bare `clang-format -i` falls back to LLVM style and reformats the entire file, splitting `if`/`return` and changing switch indentation. The spurious diff buries the real change and fails the gate, which checks with `clang-format --dry-run --Werror --style=google`.
- **C++ paths only.** clang-format formats whatever it is given as C++. A `CMakeLists.txt` comes out with `if (X)` / `set(...) else() set(...) endif()` on one line, CMake can no longer parse it, and every build job of the run fails.
- **The major.** A different major lays out some code differently, such as the closing `};` of a braced initializer that begins on its own line, so a change formatted with the wrong one fails the `clang-format` job on a line the change never meant to touch. The bare `clang-format` on the PATH is Homebrew's newest LLVM, which can be ahead of CI ([ci-toolchain-versions](ci-toolchain-versions.md)).

**How to apply:** Use `$(brew --prefix llvm@<major>)/bin/clang-format`, with the major the `major` input of `.github/actions/install-llvm/action.yml` defaults to. Name the files explicitly, or filter a list by extension first, as in `git status --porcelain | awk '{print $2}' | grep -E '\.(cpp|h)$'`. Before committing, check `git diff --stat` for a file whose line count changed unexpectedly. If the flag was missed, `git checkout` the files, re-apply the edits and format again. The `pre-push-checks` skill then runs the `--dry-run --Werror` form over the touched files ([verifying-through-ci](verifying-through-ci.md)).
