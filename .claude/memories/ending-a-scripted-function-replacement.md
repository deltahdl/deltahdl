---
name: ending-a-scripted-function-replacement
description: "When a script replaces a whole C++ function, end the old text at the closing brace in column 0, \"\\n}\\n\", never at the first \"}\\n\", which an inner block's indented brace also matches."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 0ce081b6-fd14-4da5-87da-08ca53aae436
  modified: 2026-11-21T02:50:40.298Z
---

# Ending a scripted function replacement

When a script swaps out a whole function body, find the old body's end by searching for `"\n}\n"` from the signature: the brace that closes a function under Google style stands alone in column 0. Searching for `"}\n"` stops at the first indented brace that closes an `if` or a loop inside the function.

**Why:** a search that stops early leaves the tail of the old body after the new one. The compiler then refuses the file as statements outside any function, which turns build-coverage-lib and a clang-tidy shard red and costs a push of its own to repair.

**How to apply:** after a scripted replacement, read the lines just after the new function's closing brace, then build the touched target as [verifying-through-ci](verifying-through-ci.md) describes. A brace-depth count that ends at 0 is not enough on its own, because the leftover tail can be balanced.
