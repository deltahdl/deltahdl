---
name: clang-format-only-cpp-paths
description: Never feed every path from git status to clang-format; a CMakeLists.txt or other non-C++ file in the list is rewritten as C++ and stops parsing.
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 3f978183-d158-48d4-ba7f-a20646910f29
  modified: 2026-09-20T17:28:36.333Z
---

Run `clang-format -i --style=google` on the `.cpp` and `.h` files touched, named explicitly or filtered by extension, never on `$(git status --porcelain | awk '{print $2}')` as a whole.

**Why:** On 2026-09-20 a format pass over every modified path rewrote `src/CMakeLists.txt` as C++-styled text (`if (X)` / `set(...) else() set(...) endif()` on one line), CMake failed to parse it, and every build job of the run failed. See [[clang-format-style-flag]] and [[git-add-explicit-paths]].

**How to apply:** Filter the list, e.g. `git status --porcelain | awk '{print $2}' | grep -E '\.(cpp|h)$'`, before handing it to clang-format, and review `git diff --stat` for a file whose line count changed unexpectedly before committing.
