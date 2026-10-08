---
name: braced-case-closing-brace-is-a-line
description: "A switch case written as `case X: { ...; break; }` leaves its closing brace a line llvm-cov counts and nothing runs; write the case without the block"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 0ce081b6-fd14-4da5-87da-08ca53aae436
  modified: 2026-10-08T14:59:58.772Z
---

# A braced case's closing brace is an uncovered line

`assert-coverage` counted line 215 of `src/simulator/vpi_put_value_bits.cpp` uncovered with every region and branch of the file covered. That line was the `}` of `case kVpiRealVal: { const int64_t kRounded = …; …; break; }`. The brace comes after the `break`, so no execution ever reaches it, and llvm-cov counts it as a line of the case.

**Why:** the coverage gate requires 100% of lines as well as branches. A braced case therefore keeps a file one line short however thoroughly it is tested, and an issue closed on its tests stays open in fact.

**How to apply:** when a case needs a local, move the work into a small named helper so the case is `case X: Helper(…); break;`. A `return` ending the block leaves the same brace behind, so it is no way out. When a coverage report shows one uncovered line that is only a closing brace, look for this shape first. See [[verifying-through-ci]].
