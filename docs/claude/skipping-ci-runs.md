# Skipping CI runs

When a push to `main` needs no CI cycle, include `[skip ci]` (or
`[ci skip]`) in the commit message.

A full matrix run takes 25 to 30 minutes, and `main` is configured with
`cancel-in-progress: true` grouped by ref, so every push otherwise starts
a run and cancels whatever is in flight. Skipping saves the cycle and
protects a running measurement.

Configuration-only and documentation-only commits should carry it. When
batching source fixes, mark the intermediate commits and leave it off the
last so exactly one run fires. Do not skip when the purpose of the push is
to verify, since a CI push is the only verification this repository has.
