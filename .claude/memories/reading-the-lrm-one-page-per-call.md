---
name: reading-the-lrm-one-page-per-call
description: "Read ~/IEEE 1800-2023.pdf one page per Read call, waiting for each result; batching exhausts a content-filter budget for the whole turn."
metadata:
  node_type: memory
  type: feedback
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:54:57.944Z
---

# Reading the LRM one page per call

Issue exactly one `Read` page per tool call and wait for each result before the next. Never put several PDF page reads in one message, and do not retry in bulk.

**Why:** Reading the copyrighted standard consumes a content-filter budget. Several page reads at once exhaust it immediately, and it does not recover by waiting. Once that happens, every tool result in the turn is blocked — `echo`, local file reads, all of it — and no further work is possible until a fresh turn. Two other things spend the same budget: one very large tool result ([oversized-tool-output](oversized-tool-output.md)) and text extracted from the PDF by a script ([not-converting-the-lrm-to-text](not-converting-the-lrm-to-text.md)).

**How to apply:** One page, one call, read the result, then the next. If results start coming back blocked or truncated, stop issuing calls and resume in a fresh turn rather than working blind.
