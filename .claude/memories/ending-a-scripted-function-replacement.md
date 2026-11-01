---
name: ending-a-scripted-function-replacement
description: "When a script replaces a whole C++ function, end the old text at the closing brace in column 0, \"\\n}\\n\", never at the first \"}\\n\", which an inner block's indented brace also matches."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 0ce081b6-fd14-4da5-87da-08ca53aae436
  modified: 2026-10-09T18:37:29.907Z
---

# Ending a scripted function replacement

When a script swaps out a whole function body, find the old body's end by searching for `"\n}\n"` from the signature: the brace that closes a function under Google style stands alone in column 0. Searching for `"}\n"` stops at the first indented brace that closes an `if` or a loop inside the function.

**Why:** that search left the tail of the old body after the new one twice in a row (`CallResultClass`, then `MemberIndexKind`). Each time, build-coverage-lib and a clang-tidy shard refused the file as statements outside any function, and each cost a red run and a push of its own to repair.

**How to apply:** before pushing a scripted replacement, also count the file's braces (an awk depth count ending at 0 is not enough on its own) and read the lines just after the new function's closing brace. Local builds are not run here ([[verifying-through-ci]]), so the read is the check.
