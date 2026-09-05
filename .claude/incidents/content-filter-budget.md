---
name: content-filter-budget
description: Observations of the content-filter budget that PDF reads and oversized tool results exhaust.
metadata:
  type: project
---

# What exhausting the content-filter budget looked like

Around 61 minutes of zero recovery was observed after several LRM page reads went out in one message. During it, even `echo hello` had its output suppressed, so no further work was possible until a fresh turn.

Reading the roughly 1480-line `src/simulator/vpi.h` in a single call was enough to trip the same budget on its own, with no PDF involved. Afterwards every tool result in the turn rendered as `... [truncated]`, `echo OK` included.

Calling `page.extract_text()` through `pypdf` blows it as well, and afterwards even printing the length of the result is suppressed.

The user objected to `pdftotext -layout ~/LRM.pdf` on 2026-07-01, on the separate ground that converting the PDF loses layout, tables, figures and structure.

Supports [reading-the-lrm](../rules/reading-the-lrm.md) and [oversized-tool-output](../rules/oversized-tool-output.md).
