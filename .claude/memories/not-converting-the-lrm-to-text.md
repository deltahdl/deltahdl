---
name: not-converting-the-lrm-to-text
description: Never extract or convert LRM page text; pypdf extract_text spends the content-filter budget and pdftotext loses structure.
metadata:
  node_type: memory
  type: feedback
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:55:04.047Z
---

# Not converting the LRM to text

Do not extract page text through `pypdf`, and do not convert the PDF to text at all.

**Why:** `page.extract_text()` on any page spends the content-filter budget that batched page reads spend ([reading-the-lrm-one-page-per-call](reading-the-lrm-one-page-per-call.md)), and the suppression then reaches everything else in the turn. Separately, `pdftotext` and friends lose layout, tables, figures and structure: they produce interleaved text with footers cut mid-sentence and table columns scrambled. The Read tool renders pages directly and handles figures and tables, and that path survives even after Bash output has been blocked.

**How to apply:** Read pages with the Read tool, one per call, and find them as [locating-a-clause](locating-a-clause.md) says.
