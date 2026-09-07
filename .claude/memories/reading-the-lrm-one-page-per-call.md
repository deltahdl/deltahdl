---
name: reading-the-lrm-one-page-per-call
description: Read ~/LRM.pdf one page per Read call, waiting for each result; batching exhausts a content-filter budget for the whole turn.
metadata:
  type: feedback
---

# Reading the LRM one page per call

Issue exactly one `Read` page per tool call and wait for each result before the next. Never put several PDF page reads in one message, and do not retry in bulk.

**Why:** Reading the copyrighted standard consumes a content-filter budget. Several page reads at once exhaust it immediately, and it does not recover by waiting. Once that happens, every tool result in the turn is blocked — `echo`, local file reads, all of it — and no further work is possible until a fresh turn.

**How to apply:** One page, one call, read the result, then the next. The same budget is spent by a single very large tool result, so see [oversized-tool-output](oversized-tool-output.md), and by `pypdf` text extraction, so see [not-converting-the-lrm-to-text](not-converting-the-lrm-to-text.md).
