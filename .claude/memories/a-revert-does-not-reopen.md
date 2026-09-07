---
name: a-revert-does-not-reopen
description: Reverting a commit leaves the issue it closed closed; reopen it by hand with gh issue reopen.
metadata:
  type: project
---

# A revert does not reopen what the commit closed

Reopen the issue by hand when a revert takes back the commit that closed it.

**Why:** GitHub closes on the keyword reaching the default branch and has nothing to undo it. `git revert` writes a new commit, the original stays in history, and a revert message saying `Refs #N` or even naming the revert leaves `#N` closed and marked completed. The failure is quiet in both directions: the tracker shows work that was finished, the tree contains none of it, and the selector that lists open issues will never offer it again — so the next session reads a closed issue with a diagnosis comment on it and no way to arrive there. `5b1bcd5b1` reverted `0f07bf9b5` and #3469 stayed closed until the loop noticed the number missing from its own listing.

**How to apply:** A revert is two steps. Push the revert, then `gh issue reopen <N>` with a comment saying which commit closed it, which one took it back, and what the run said. Read the state back with `gh issue view <N> --json state`, because the revert's own message gives no evidence either way.
