---
name: positive-prompts
description: "Phrase a prompt the repository writes for a session, such as a skill's instructions or an autopilot reminder, as the action wanted rather than the one forbidden."
metadata:
  node_type: memory
  type: feedback
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:54:30.786Z
---

# Positive phrasing in written prompts

Prefer positive instructions to prohibitions in the prompts this repository writes for a session to follow: a skill's instructions under `.claude/skills/`, and the reminders the autopilot skill schedules.

**Why:** Models follow "do X" more reliably than "don't do Y", because negation tends to surface the prohibited idea without suppressing it. Nothing enforces the choice; a prompt written the other way still runs.

**How to apply:** Lead with the capability and how to use it — "The Read tool decodes PDFs natively; pass `pages: "N"` to read page N". Leave prohibitions to something that can enforce them, such as a PreToolUse hook or the `permissions.deny` list in `.claude/settings.json`. If a "don't" or "never" is being written into a prompt body, restate it as the action that is wanted instead.
