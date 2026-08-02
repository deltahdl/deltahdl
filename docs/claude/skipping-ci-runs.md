# Skipping CI runs

Put `[skip ci]` (or `[ci skip]`) on a push that no workflow is configured to observe, and on nothing else.

A full matrix run takes 25 to 30 minutes, and `main` is configured with `cancel-in-progress: true` grouped by ref, so a push that starts a run cancels whatever is in flight. Skipping saves the cycle and protects a running measurement.

Read the `on:` triggers under `.github/workflows/` to decide whether a push needs a run. They watch paths. The kind of file is not an answer: a repository grows a workflow for its documentation, its configuration, its schemas, and the moment it does, "documentation-only" stops meaning "ungated". `[skip ci]` suppresses every workflow at once. A commit skipped on the grounds that the matrix has nothing to say about it therefore also skips the linter that exists for exactly those files, and the push lands unchecked by the one gate that was watching.

Leave `[skip ci]` off where the triggers already exclude a push. The run does not start either way, and writing it implies a judgement that was never made.

When batching source fixes, mark the intermediate commits and leave it off the last, so exactly one run fires. Never skip when the purpose of the push is to verify, since a CI push is the only verification this repository has.

An earlier version of this note said configuration-only and documentation-only commits should carry it. That was written when nothing gated Markdown, stayed on the page after `documentation.yml` began linting it, and was still being quoted on 2026-08-01 to propose skipping the very run a documentation change exists to trigger. A convention that names the current shape of the gates rather than the authority over them fails exactly this way — see [docs/tenets/conventions/README.md](../tenets/conventions/README.md).
