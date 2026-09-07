---
name: module-terms-in-descriptions
description: Describe a change to a module in that module's own terms, not its callers'.
metadata:
  type: feedback
---

# Describing a change in the module's own terms

Describe a change to a module in that module's own terms: a docstring, comment, error message or commit message in module M should make sense to a reader who has never heard of anything that calls M.

**Why:** Nothing enforces this, and naming the caller reads as helpful context at the time of writing. It stops being true as soon as a second caller exists, and it makes the module's own documentation unreadable to anyone arriving from a third direction.

**How to apply:** When writing about a change in M, name what M does. If the reason only makes sense as "because the pipeline needs it", the note belongs with the pipeline instead.
