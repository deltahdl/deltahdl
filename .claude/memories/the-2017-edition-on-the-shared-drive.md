---
name: the-2017-edition-on-the-shared-drive
description: IEEE 1800-2017 is `~/IEEE 1800-2017.pdf`, a symbolic link to the copy on the 10U Labs shared drive; read it only to judge an sv-tests tag in its own edition, physical page = printed + 1
metadata:
  type: reference
---

# The 2017 edition on the shared drive

`~/IEEE 1800-2017.pdf` is IEEE 1800-2017. It is a symbolic link the user
asked for on 2026-09-21, pointing at the copy in the Standards folder of the
10U Labs shared drive (Google Drive), where `1800-2023.pdf` beside it is the
same edition as `~/LRM.pdf`; the repository, its memories and its issues name
the link, never the drive path. Its contents pages run from physical page 8,
and a body page's physical number is its printed number plus one, as in the
2023 copy. Read it one page per call, as [[reading-the-lrm-one-page-per-call]]
says for the 2023 copy.

**Why:** sv-tests tags its tests by 1800-2017, so whether a tag is wrong in
its own edition — as against merely renumbered in 2023 — can only be settled
from the 2017 text. On 2026-09-21 the user asked, of #3637, whether the tag
had been checked against 2017 at all; it had not, the session having no copy,
and the user pointed to this one. The check confirmed the tag-mismatch
issues #3636, #3637, #3638 and #3639: each tag is wrong or beside the rule
in 2017 as in 2023.

**How to apply:** open it to answer what a 2017 clause number names or where
a 2017 rule sits, and say in the issue which physical page of which edition
was read. Nothing from it reaches deltahdl's behaviour, reports or tests:
[[single-edition-1800-2023]] still holds, and the translation of a 2017 tag
belongs to `_SUBCLAUSE_OF_TAG` in `scripts/run_sv_tests` alone.
