# Skipping CI runs

`[skip ci]` (or `[ci skip]`) belongs on a push that no workflow is
configured to observe, and on nothing else.

A full matrix run takes 25 to 30 minutes, and `main` is configured with
`cancel-in-progress: true` grouped by ref, so a push that starts a run
cancels whatever is in flight. Skipping saves the cycle and protects a
running measurement.

What decides whether a push needs a run is the set of `on:` triggers under
`.github/workflows/`, which watch paths. Read them. A kind of file is not
an answer: a repository grows a workflow for its documentation, its
configuration, its schemas, and the moment it does, "documentation-only"
stops meaning "ungated". `[skip ci]` suppresses every workflow at once, so
a commit skipped on the grounds that the matrix has nothing to say about
it also skips the linter that exists for exactly those files, and the push
lands unchecked by the one gate that was watching.

Where the triggers already exclude a push, `[skip ci]` adds nothing: the
run does not start either way, and writing it implies a judgement that was
never made.

When batching source fixes, mark the intermediate commits and leave it off
the last, so exactly one run fires. Do not skip when the purpose of the
push is to verify, since a CI push is the only verification this
repository has.

An earlier version of this note said configuration-only and
documentation-only commits should carry it. That was written when nothing
gated Markdown, stayed on the page after `documentation.yml` began linting
it, and was still being quoted on 2026-08-01 to propose skipping the very
run a documentation change exists to trigger. A convention that names the
current shape of the gates rather than the authority over them fails
exactly this way — see
[docs/tenets/conventions/README.md](../tenets/conventions/README.md).
