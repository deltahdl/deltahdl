---
name: module-terms-in-descriptions
description: Describe a change to a module in that module's own terms, not its callers'.
metadata:
  type: feedback
---

# Describing a change in the module's own terms

Describe a change to a module in that module's own terms: an error message or commit message about module M should make sense to a reader who has never heard of anything that calls M. Docstrings and comments are not among the places: the assert-no-comments job in `.github/workflows/scripts.yml` refuses both under lib/python, scripts, their tests and the workflow itself; see [[no-comments-or-docstrings-in-python]].

**Why:** Nothing enforces this, and naming the caller reads as helpful context at the time of writing. It stops being true as soon as a second caller exists, and it makes the module's own documentation unreadable to anyone arriving from a third direction.

**How to apply:** When writing about a change in M, name what M does. If the reason only makes sense as "because the pipeline needs it", the note belongs with the pipeline instead.
