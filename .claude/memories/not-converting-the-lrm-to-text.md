---
name: not-converting-the-lrm-to-text
description: Never extract or convert LRM page text; pypdf extract_text spends the content-filter budget and pdftotext loses structure.
metadata:
  type: feedback
---

# Not converting the LRM to text

Do not bulk-extract page text through `pypdf`, and do not convert the PDF to text at all.

**Why:** Calling `page.extract_text()` on any page blows the same content-filter budget that batched page reads do, and the suppression then reaches everything else in the turn. Separately, `pdftotext` and friends lose layout, tables, figures and structure: they produce interleaved text with footers cut mid-sentence and table columns scrambled. The Read tool renders pages directly and handles figures and tables, and that path survives even after Bash output has been poisoned.

**How to apply:** Read pages with the Read tool, one per call, per [reading-the-lrm-one-page-per-call](reading-the-lrm-one-page-per-call.md). A Bash deny hook already blocks `pdftotext`, `pdfgrep`, `pdftohtml`, `pdftoppm` and `mutool`; it allows `pdfinfo` and `python3` with `pypdf`, which is what makes the metadata-only outline walk in [locating-a-clause](locating-a-clause.md) available and `extract_text()` a live hazard.
