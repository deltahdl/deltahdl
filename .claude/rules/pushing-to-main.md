# Pushing to main

Commit directly to `main`. Do not frame work as pull requests, do not suggest opening one, and do not structure advice around review cycles. The user stated it plainly — "we push to main. we dont do PRs" — and `git log --merges` on `main` is empty.

Use commits as the unit when breaking work down, and think in commit ordering rather than branch-and-merge. Two consequences follow. A closing keyword in a commit title fires the moment it is pushed. CI is the only review buffer there is.

Related: [commit-message-width](../conventions/commit-message-width.md) for the form a message takes.
