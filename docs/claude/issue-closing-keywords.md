# Issue-closing keywords in commit messages

GitHub closes any issue referenced as `fix`, `fixes`, `fixed`, `close`, `closes`, `closed`, `resolve`, `resolves` or `resolved` followed by `#N`, anywhere in a commit message pushed to the default branch. Brackets do not disable it: `Fix the gate (#N)` is read as `fix #N` and closes the issue.

That happened. A commit titled `Fix <script>'s implementability gate (#N)` was written to name the bug being worked on, not to finish it. GitHub closed the issue on push, before the verification run had happened, and it had to be reopened. The close and the reopen twelve minutes later are both still in that issue's timeline.

When a commit only references an issue, use `Refs #N`, `See #N`, a bare `#N` with no keyword before it, or rephrase the title. Reserve the closing keyword for the commit that genuinely finishes the issue, and write it as `Closes #N`. That is the form the history uses — 3343 commits open a line with `Closes #N` against 11 with `Fixes #N`.

Repeat the keyword on its own line for each issue a commit finishes. A keyword binds to exactly one number, so `Closes #N, #M, #P` closes the first and leaves the rest open while reading as though it closed all three:

```text
Closes #N
Closes #M
Closes #P
```

That form has closed ten issues in a single commit here. After a multi-issue close, read the states back with `gh issue view <N> --json state` rather than trusting the shape of the message.
