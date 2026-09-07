---
name: recording-what-a-session-learns
description: Write what a session learns into .claude/memories/ as one indivisible fact per file, with a line in MEMORY.md.
metadata:
  type: feedback
---

# Recording what a session learns

Write it down in `.claude/memories/`, one fact per file, and add a line for it to `MEMORY.md`.

**Why:** `.claude/memories/` is the whole of the notes now. `CLAUDE.md`, `rules/`, `conventions/` and `references/` were collapsed into it on 2026-09-07 at the user's instruction — see [note-directories](note-directories.md) for what that changed. One fact per file is what makes a note retrievable: recall selects whole files, so a file carrying two facts is either pulled in when only one of them is wanted or missed when the other is.

**How to apply:** Give the file front matter with `name`, a one-line `description`, and `metadata.type` of `user`, `feedback`, `project` or `reference`. A `feedback` or `project` memory follows its opening statement with **Why:** and **How to apply:** lines. Open the body with a top-level heading, per [markdown-top-level-heading](markdown-top-level-heading.md). Link related memories with `[[name]]` or a Markdown link; link liberally, since a link to a memory that does not exist yet marks something worth writing.

A note earns its place by changing what a session would otherwise get wrong. Do not record what the repository already carries — code structure, past fixes, git history. What only explains why a rule is right belongs in that rule's **Why:**, not in a file of its own. Before writing, check whether a memory already covers the fact and update that one instead; delete a memory that turns out to be wrong.
