---
name: clang-format-only-cpp-paths
description: Never feed every path from git status to clang-format; a CMakeLists.txt or other non-C++ file in the list is rewritten as C++ and stops parsing.
metadata:
  type: feedback
---

# clang-format on C++ paths only

Run `clang-format -i --style=google` on the `.cpp` and `.h` files touched, named explicitly or filtered by extension, never on `$(git status --porcelain | awk '{print $2}')` as a whole.

**Why:** clang-format formats whatever it is given as C++: a `CMakeLists.txt` comes out with `if (X)` / `set(...) else() set(...) endif()` on one line, CMake can no longer parse it, and every build job of the run fails. See [[clang-format-style-flag]] and [[git-add-explicit-paths]].

**How to apply:** Filter the list, e.g. `git status --porcelain | awk '{print $2}' | grep -E '\.(cpp|h)$'`, before handing it to clang-format, and review `git diff --stat` for a file whose line count changed unexpectedly before committing.
