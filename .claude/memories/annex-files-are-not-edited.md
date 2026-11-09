---
name: annex-files-are-not-edited
description: "src/simulator/vpi_user.h is Annex K.2's text and is never edited, even for a platform the annex's portability help misses; the shim goes in the build."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 71fdefb1-3397-48b8-838f-7c5e17be7223
  modified: 2026-11-08T02:14:20.527Z
---

# Annex files are not edited

`src/simulator/vpi_user.h` is the file Annex K.2 prints and holds nothing of the repository's own; a platform problem in it is solved outside the file.

**Why:** The text is the standard's, and a departure in it, however small, is a departure from the source of truth ([lrm-source-of-truth](lrm-source-of-truth.md)).

**How to apply:** Leave the annex's text byte for byte. When a platform needs something ahead of the file, give it from the build (`CMakeLists.txt` passes `-include stdint.h` on APPLE, where the annex's `<sys/types.h>` fallback leaves `uint64_t` undeclared) or from the translation unit that reads the file, never from inside it. The same holds for the other five annex headers in `src/simulator/`: `sv_vpi_user.h`, `vpi_compatibility.h`, `svdpi.h`, `svdpi_src.h` and `svdpi_sv31a.h`. The `assert-lrm-mandated-files` job in `.github/workflows/deltahdl.yml` pins each one by its SHA-256 and fails when the content departs from the pin. A change to one of them is a re-verification against the annex's printed pages and a new pin in the same commit, and nothing else. A check that the annex's text trips is excluded from the file, as `ExcludeHeaderFilterRegex` in both clang-tidy configurations does for all six, never fixed inside it. Their comments are the standard's text and stay, as one of the exceptions in [no-comments-in-any-file](no-comments-in-any-file.md). See [include-what-you-use](include-what-you-use.md) for the annex file being the one C include.
