# Reading the LRM without blocking the turn

Issue exactly one `Read` page per tool call and wait for each result before the next. Never put several PDF page reads in one message, and do not retry in bulk.

Reading the copyrighted standard consumes a content-filter budget. Several page reads at once exhaust it immediately, and it does not recover by waiting: around 61 minutes of zero recovery was observed, during which even `echo hello` had its output suppressed. Once that happens, every tool result in the turn is blocked and no further work is possible until a fresh turn.

Do not bulk-extract page text through `pypdf`. Calling `page.extract_text()` on any page blows the same budget, and afterwards even printing the length of the result is suppressed. The suppression then reaches everything else in the turn: `echo`, local file reads, all of it.

Do not convert PDFs to text at all. `pdftotext` and friends lose layout, tables, figures and structure, and produce interleaved text with footers cut mid-sentence and table columns scrambled. The user objected to `pdftotext -layout ~/LRM.pdf` on 2026-07-01. The Read tool renders pages directly and handles figures and tables, and that path survives even after Bash output has been poisoned.
