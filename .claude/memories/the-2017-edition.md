---
name: the-2017-edition
description: IEEE 1800-2017 is `~/IEEE 1800-2017.pdf`; read it only to judge an sv-tests tag in its own edition, physical page = printed + 1
metadata:
  type: reference
---

# The 2017 edition

`~/IEEE 1800-2017.pdf` is IEEE 1800-2017. A body page's physical number is
its printed number plus one. Read it one page per call, as
[[reading-the-lrm-one-page-per-call]] says for `~/LRM.pdf`.

**Why:** sv-tests tags its tests by 1800-2017, so whether a tag is wrong in
its own edition, rather than renumbered in 2023, is settled from the 2017
text alone.

**How to apply:** open it to answer what a 2017 clause number names or where
a 2017 rule sits, and say in the issue which physical page of which edition
was read. Nothing from it reaches deltahdl's behaviour, reports or tests:
[[single-edition-1800-2023]] still holds, and the translation of a 2017 tag
belongs to `_SUBCLAUSE_OF_TAG` in `scripts/run_sv_tests` alone.
