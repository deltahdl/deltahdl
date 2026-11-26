---
name: commit-body-left-unwrapped
description: "A commit body writes each paragraph on one line, never hard-wrapped at a column; a paragraph never runs onto a second line."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 13120786-5e0a-4960-8b6a-9e4c6c5687bf
  modified: 2026-11-21T11:41:34.081Z
---

# A commit body is left unwrapped

Write each paragraph of a commit body as a single line, however long, with a blank line between paragraphs. Only a trailer (`Closes #N`, `Refs #N`, `See #N`, `Co-Authored-By:`), a list item or an indented line may sit directly under another line.

**Why:** A body broken at a column is broken for one width alone. GitHub, a narrow terminal and every other view lay it out again at their own width, so its fixed breaks land mid-line and leave ragged fragments, while a paragraph on one line flows to whatever width it is read at. Wrapping at 72 is the habit git's own documentation teaches, so it comes back whenever nothing in view says otherwise; it is the general rule of [prose-length-over-column-fitting](prose-length-over-column-fitting.md) applied to the one place in a commit with room.

**How to apply:** Keep the subject to 72 characters or fewer, naming the change, and put the detail in the body. Read the message back with `git log -1` before pushing, and reword a body whose prose line follows another prose line with `git commit --amend -F -`, since a pushed message stays as it is. The closing lines follow [closing-keywords](closing-keywords.md).
