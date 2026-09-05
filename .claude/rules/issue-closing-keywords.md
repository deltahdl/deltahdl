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

Related: [closing-keyword-in-a-title](../memories/closing-keyword-in-a-title.md) for the issue this closed by accident.
