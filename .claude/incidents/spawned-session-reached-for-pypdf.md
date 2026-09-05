---
name: spawned-session-reached-for-pypdf
description: A spawned session bypassed a "Read with the Read tool" hint and reached for pypdf through Bash, which is what prompted the positive-phrasing rule.
metadata:
  type: feedback
---

# The hint a spawned session walked straight past

A spawned session bypassed a "Read with the Read tool" hint in its generated prompt and reached for `pypdf` through Bash instead. The user pointed out afterwards that a model follows "do X" more reliably than "don't do Y", because negation tends to surface the prohibited idea without suppressing it.

Supports [positive-prompts](../conventions/positive-prompts.md).
