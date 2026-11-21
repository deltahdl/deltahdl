---
name: gate-limits-live-in-tracked-files
description: "The CI gates take their limits from tracked files, the clang-tidy configurations and the workflow; read a limit there, never from a tool default or a note."
metadata:
  node_type: memory
  type: feedback
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:52:06.772Z
---

# Gate limits live in tracked files

Check a change against a gate's limit by reading the tracked file that sets it.

**Why:** The gates take their limits from the repository, not from a tool's defaults, and a note that restated a number would go stale the day the file changed. The file is the authority.

**How to apply:**

- `etc/clang_tidy/src.yml` and `etc/clang_tidy/test_src_unit.yml` set the naming rules ([const-local-naming](const-local-naming.md)) and the function-size, nesting, parameter and cognitive-complexity thresholds, which differ between the two ([clang-tidy-test-config-mirrors-src](clang-tidy-test-config-mirrors-src.md)).
- `.github/workflows/deltahdl.yml` sets the copy-paste detectors' token count ([sharing-code-a-change-mirrors](sharing-code-a-change-mirrors.md)) and the file-line cap. The cap fails a `.cpp` or `.h` under `src`, `test` or `lib/cpp` above 1000 lines, so 1000 is the most such a file may hold, and it has no warning band below it. A file near the cap is split before a change adds to it, rather than squeezed shorter ([prose-length-over-column-fitting](prose-length-over-column-fitting.md), [test-file-letter-suffixes](test-file-letter-suffixes.md)).
- The `pre-push-checks` skill checks the touched files against the clang-tidy limits and the line cap before a push; the copy-paste detectors run only in CI ([verifying-through-ci](verifying-through-ci.md)).
