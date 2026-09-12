---
name: lrm-text-is-copyrighted
description: The LRM's text is IEEE copyright, so a comment, test or commit message paraphrases a clause rather than quoting it verbatim.
metadata:
  type: feedback
---

# The LRM's text is copyrighted

Do not put the LRM's text verbatim in comments. IEEE 1800-2023 is copyrighted, and its sentences do not belong in this repository — not in a source comment, a test comment, a commit message or a memory. Cite the clause by number and state its rule in your own words.

**Why:** The user's instruction on 2026-09-12: the LRM's text is copyrighted, so we cannot put it verbatim in comments. Publishing the standard's sentences in a public tree redistributes them; a paraphrase carries the rule without the text.

**How to apply:** Write `§21.3.6 has a regular file's output stay buffered until $fflush or $fclose` rather than the clause's own sentence in quotation marks. A term the standard defines — a keyword, a system task name, a word like "stop_value" — is not a quotation and may be used as is. The clause number is still required, per [naming-the-report-in-a-rejection-test](naming-the-report-in-a-rejection-test.md), and the clause is still what decides the behaviour, per [lrm-source-of-truth](lrm-source-of-truth.md); what changes is that the words explaining it are yours. The tree written before this rule quotes freely; rewrite a quotation the change in hand touches, and ask before sweeping the rest.
