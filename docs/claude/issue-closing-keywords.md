# Issue-closing keywords in commit messages

GitHub closes any issue referenced as `fix`, `fixes`, `fixed`, `close`,
`closes`, `closed`, `resolve`, `resolves` or `resolved` followed by `#N`,
anywhere in a commit message pushed to the default branch. Brackets do not
disable it: `Fix the gate (#878)` is read as `fix #878` and closes the
issue.

That happened. `Fix implement_subclause's implementability gate (#878)`
was written to reference #878 as the bug being worked on. GitHub closed it
on push, before the verification run had happened, and it had to be
reopened — still visible in the timeline of #878, closed by `be31882e4`
and reopened twelve minutes later.

When a commit only references an issue, use `Refs #N`, `See #N`, a bare
`#N` with no keyword before it, or rephrase the title. Reserve
`Fixes #N` and `Closes #N` for the commit that genuinely finishes the
issue.
