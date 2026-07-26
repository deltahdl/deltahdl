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
`#N` with no keyword before it, or rephrase the title. Reserve the
closing keyword for the commit that genuinely finishes the issue, and
write it as `Closes #N`. That is the form the history uses — 3343
commits open a line with `Closes #N` against 11 with `Fixes #N`.

The mirror image of that trap is a comma-separated list. A keyword binds
to exactly one `#N`, so `Closes #2830, #2832, #2833` closes #2830 and
leaves the other two open while reading as though it closed all three.
A commit that finishes several issues needs the keyword repeated, one
per line:

```text
Closes #2830
Closes #2832
Closes #2833
```

`0a57ba429` closed ten issues in that one-per-line form. After a
multi-issue close, read the states back with
`gh issue view <N> --json state` rather than trusting the shape of the
message.
