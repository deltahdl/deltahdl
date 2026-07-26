# Where a new note belongs

A working convention learned in a session goes into this repository, not
into the session tool's local memory directory. `CLAUDE.md` carries the
short form, one paragraph under the matching heading; `docs/claude/` gets
the long form as one file per topic, linked from `CLAUDE.md` and from
`docs/claude/README.md`. Both are read at the start of a session, and
both travel with the code.

The local memory directory holds one machine's files. Nothing versions
them, nothing reviews them, and nobody else ever sees them. A rule
written only there is lost with the machine, and a rule written in both
places drifts: on 2026-07-26 the twenty notes were copied into the
repository at 10:45, a rule about comma-separated closing keywords was
added to the local copy at 11:22, and the two disagreed from that moment
with nothing to signal it. That is issue #2829, and it is why the local
copies were deleted.

What stays local is what is true only of this machine and useless
elsewhere. The standing one is the retention rule: per-subclause
satisfaction state belongs in the GitHub issue and in `git log`, never in
a memory file, so a memory that turns out to be a per-subclause write-up
is retired rather than repaired. Sessions the pipeline spawns write no
memories at all — `build_env` and `write_deny_hook_settings` in
`lib/python/claude_cli_streaming` turn auto-memory off from both
directions.

When a correction arrives mid-session, edit the note in `docs/claude/`
and commit it. A documentation-only commit carries `[skip ci]`.
