# Issue-closing keywords in commit messages

GitHub closes any issue referenced as `fix`, `fixes`, `fixed`, `close`, `closes`, `closed`, `resolve`, `resolves` or `resolved` followed by `#N`, anywhere in a commit message pushed to the default branch. Brackets do not disable it: `Fix the gate (#N)` is read as `fix #N` and closes the issue.

Reserve a closing keyword for the commit that genuinely finishes the issue. Where a commit only references one, use a non-closing word or rephrase the title; [closing-keyword-form](../conventions/closing-keyword-form.md) gives the words this repository writes for each case.

Repeat the keyword on its own line for each issue a commit finishes. A keyword binds to exactly one number, so `Closes #N, #M, #P` closes the first and leaves the rest open while reading as though it closed all three:

```text
Closes #N
Closes #M
Closes #P
```

That form has closed ten issues in a single commit here. After a multi-issue close, read the states back with `gh issue view <N> --json state` rather than trusting the shape of the message.

## Reverting a commit does not reopen what it closed

Reopen the issue by hand when a revert takes back the commit that closed it. GitHub closes on the keyword reaching the default branch and has nothing to undo it: `git revert` writes a new commit, the original stays in history, and a revert message saying `Refs #N` or even naming the revert leaves `#N` closed and marked completed.

The failure is quiet in both directions. The tracker shows work that was finished, the tree contains none of it, and the selector that lists open issues will never offer it again — so the next session reads a closed issue with a diagnosis comment on it and no way to arrive there. `5b1bcd5b1` reverted `0f07bf9b5` and #3469 stayed closed until the loop noticed the number missing from its own listing.

So a revert is two steps. Push the revert, then `gh issue reopen <N>` with a comment saying which commit closed it, which one took it back, and what the run said. Read the state back with `gh issue view <N> --json state`, the same way [a multi-issue close](#issue-closing-keywords-in-commit-messages) is read back, because the revert's own message gives no evidence either way.
