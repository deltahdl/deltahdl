---
name: issue-sections-take-headings
description: "Mark each section of an issue body with a Markdown heading (## The defect), never by bolding its first sentence"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 31a6b48c-0ebd-473c-a398-53773533f58e
  modified: 2026-09-28T23:01:36.313Z
---

# Issue sections take headings

When an issue body falls into sections, open each with a Markdown heading —
`## The defect`, `## What the standard asks`, `## The fix wanted` — on its own
line, with the section's prose starting below it. Never mark a section by
bolding its opening words inline, as in `**The defect.** deltahdl accepts…`.

**Why:** the user prefers headings: they render as real structure on GitHub,
show in the outline, and can be linked to, where a bolded lead sentence is
only emphasis run into the paragraph.

**How to apply:** use `##` for sections, since the issue title stands above
them; a short noun phrase for the heading, no trailing period. When editing an
issue written with bolded leads, convert them to headings. This is the one
formatting rule for issues; otherwise [[issues-have-no-fixed-form]] holds.
