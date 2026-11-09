---
name: recording-what-a-session-learns
description: Write what a session learns into .claude/memories/ as one indivisible fact per file, with a line in MEMORY.md.
metadata:
  type: feedback
---

# Recording what a session learns

Write it down in `.claude/memories/`, one fact per file, and add a line for it to `MEMORY.md`.

**Why:** `.claude/memories/` is the whole of the notes — see [note-directories](note-directories.md). One fact per file is what makes a note retrievable: recall selects whole files, so a file carrying two facts is either pulled in when only one of them is wanted or missed when the other is.

**How to apply:** Give the file front matter with `name`, a one-line `description`, and `metadata.type` of `user`, `feedback`, `project` or `reference`. A `feedback` or `project` memory follows its opening statement with **Why:** and **How to apply:** lines. Open the body with a top-level heading, per [markdown-top-level-heading](markdown-top-level-heading.md). Link a related memory with a Markdown link to its file, `[name](name.md)`, the slug as its text, and never with `[[name]]`: the notes are Markdown files read on GitHub and in a browser, where that form is plain text and leads nowhere. Link liberally, but only to a file that exists, so that every link opens one.

A note earns its place by changing what a session would otherwise get wrong. Do not record what the repository already carries — code structure, past fixes, git history. A note carries no history of its own either: its **Why:** gives the reason for the rule, not when, by whom or after what incident it was set, and a rule that changes is rewritten, not annotated with what it used to say; the log keeps all of that. What only explains why a rule is right belongs in that rule's **Why:**, not in a file of its own. Before writing, check whether a memory already covers the fact and update that one instead; delete a memory that turns out to be wrong.
