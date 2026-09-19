---
name: annex-files-are-not-edited
description: "src/simulator/vpi_user.h is Annex K.2's text and is never edited, even for a platform the annex's portability help misses; the shim goes in the build."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 7829aa59-f8bc-4f09-b395-224467199b68
  modified: 2026-09-19T16:38:22.970Z
---

# Annex files are not edited

`src/simulator/vpi_user.h` is the file Annex K.2 prints and holds nothing of the repository's own; a platform problem in it is solved outside the file.

**Why:** On 2026-09-19 the annex's `<sys/types.h>` fallback left `uint64_t` undeclared on macOS and I added `__APPLE__` to its `#elif defined(__linux)` line; the user asked "isn't that file supposed to never be modified besides what the LRM provides?", and it is. The text is the standard's, and a departure in it, however small, is a departure from the source of truth ([[lrm-source-of-truth]]).

**How to apply:** Leave the annex's text byte for byte. When a platform needs something ahead of the file, give it from the build (`CMakeLists.txt` passes `-include stdint.h` on APPLE for this one) or from the translation unit that reads the file, never from inside it. The same holds for `sv_vpi_user.h` (K.3) and `svdpi.h`, whose repository comments explain rather than alter the annex's text. See [[include-what-you-use]] for the annex file being the one C include.
