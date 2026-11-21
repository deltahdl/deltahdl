---
name: gh-search-returns-at-most-1000-issues
description: "gh issue list with --search, or with --limit 1000, silently drops every open issue older than the newest 1000; list them all with --limit 10000 and no --search, filtering labels in jq"
metadata:
  node_type: memory
  type: reference
  originSessionId: 86699205-8167-4d43-95d1-668dd7cf1a13
  modified: 2026-11-21T02:52:37.379Z
---

# gh search returns at most 1000 issues

`gh issue list --search …` goes through GitHub's search API, which returns at most 1000 results whatever `--limit` asks for. A listing with `--search`, or one without it at `--limit 1000`, therefore holds only the newest 1000 open issues. Once more are open, every older one is left out without a word, and a loop reading such a listing never sees them.

**Why:** A loop that picks the next clause or issue from such a listing moves past older issues that are still open, as if their work were done.

**How to apply:** List open issues with `gh issue list --state open --limit 10000` and no `--search`. That form pages through GraphQL and returns them all. Leave a label out inside the `--jq` program with `map(select(all(.labels[]; .name != "<label>")))`. When a listing's length comes back as exactly its limit, the listing was cut short. The autopilot skill's loop commands follow this; see [the autopilot skill](../skills/autopilot/SKILL.md).
