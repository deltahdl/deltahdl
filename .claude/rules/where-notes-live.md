# Where a new note belongs

Put a working convention learned in a session into this repository, and never into a directory outside it. `.claude/CLAUDE.md` carries the short form, one paragraph under the matching heading. `.claude/rules/` gets the long form as one file per topic, linked from `.claude/CLAUDE.md`. Both are read at the start of a session, and both travel with the code.

`.claude/rules/` is where a person writes a rule. `.claude/memories/` is where the session tool writes one by itself: `.claude/settings.json` sets `autoMemoryEnabled` to `true` and `autoMemoryDirectory` to `.claude/memories/`, so an automatic memory is written inside the working tree and is committed, reviewed and diffed like any other file. Neither directory is the session tool's default local memory directory, which is `~/.claude/projects/<slug>/memory/` and outside any repository.

Nothing outside the repository is versioned, reviewed, or seen by anybody else, so a rule written there is lost with the machine. A rule written in two places drifts instead: on 2026-07-26 the twenty notes were copied into the repository at 10:45, a rule about comma-separated closing keywords was added to the local copy at 11:22, and the two disagreed from that moment with nothing to signal it. That is why the local copies were deleted, and why `autoMemoryDirectory` now names a path the repository tracks rather than leaving the default in place.

A session that `scripts/satisfy_subclause/mutators.py` spawns writes no memory at all, whatever this repository's settings say. `build_env` and `write_deny_hook_settings` in `lib/python/claude_cli_streaming` turn auto-memory off from both directions for those sessions, because one such run wrote a memory per subclause, duplicating satisfaction state the tracking issue and `git log` already own. That exception is about a batch of unattended sessions, and it does not extend to a session started by hand.

When a correction arrives mid-session, edit the note in `.claude/rules/` and commit it.
