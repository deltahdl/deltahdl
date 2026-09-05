# Where a new note belongs

Put a working convention learned in a session into this repository, not into the session tool's local memory directory. `CLAUDE.md` carries the short form, one paragraph under the matching heading. `.claude/memories/` gets the long form as one file per topic, linked from `CLAUDE.md` and from `.claude/memories/README.md`. Both are read at the start of a session, and both travel with the code.

`.claude/memories/` is tracked by git and is not the session tool's local memory directory, whatever the two names suggest. The local one is `~/.claude/projects/<slug>/memory/`, outside any repository.

The local memory directory holds one machine's files. Nothing versions them, nothing reviews them, and nobody else ever sees them. A rule written only there is lost with the machine. A rule written in both places drifts: on 2026-07-26 the twenty notes were copied into the repository at 10:45, a rule about comma-separated closing keywords was added to the local copy at 11:22, and the two disagreed from that moment with nothing to signal it. That is why the local copies were deleted.

Write nothing to the local memory directory. `.claude/settings.json` sets `autoMemoryEnabled` to `false`, so a session rooted in this repository writes no memory of its own, and the one index file the directory held is deleted. What that setting prevents is on record: a session spawned by `scripts/satisfy_subclause/mutators.py` wrote one memory per subclause, duplicating satisfaction state the tracking issue and `git log` already own, which is why `build_env` and `write_deny_hook_settings` in `lib/python/claude_cli_streaming` turn auto-memory off from both directions for those sessions. The tracked setting extends the same rule to a session started by hand.

When a correction arrives mid-session, edit the note in `.claude/memories/` and commit it.
