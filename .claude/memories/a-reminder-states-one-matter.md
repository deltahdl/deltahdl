---
name: a-reminder-states-one-matter
description: "Each autopilot reminder states one indivisible matter and fires every 15 minutes; a rule naming two matters is written as two reminders."
metadata:
  type: feedback
---

# A reminder states one matter

Each reminder in `.claude/skills/autopilot/SKILL.md` states one indivisible matter, and fires every 15 minutes. A text that names two matters is written as two reminders.

**Why:** A matter sharing a reminder with another is read past, or lost when the text around it is rewritten.

**How to apply:** Reread every reminder when one is added or changed, and split any that two unrelated sessions could each follow half of. Reminders may share a minute, so they are told apart by their text. Steps of one action, such as listing issues and taking the first, are one matter. Phrase each per [positive-prompts](positive-prompts.md).
