---
name: path-filters-spell-out-the-dot
description: "A GitHub Actions paths pattern matches inside a dot-prefixed directory such as .claude/ only where the pattern writes the dot, so '**/*.md' alone never starts a run for the notes."
metadata:
  node_type: memory
  type: reference
  originSessionId: 71fdefb1-3397-48b8-838f-7c5e17be7223
  modified: 2026-11-08T02:13:59.708Z
---

# Path filters spell out the dot

In a workflow's `on.push.paths`, `**` does not descend into a directory whose name starts with a dot. `'**/*.md'` matches no file under `.claude/`, and `'**/*.json'` doesn't match `.claude/settings.json`.

**Why:** Before `markdownlint.yml` named `.claude/**/*.md`, eight pushes that changed nothing but `.claude/skills/autopilot/SKILL.md` started no run at all, so the notes went unlinted.

**How to apply:** For each file type a workflow checks, add a second entry that writes the dot directory out, as `markdownlint.yml` (`.claude/**/*.md`) and `jsonlint.yml` (`.claude/**/*.json`) do. A single file, such as `.claude/statusline.sh`, is named in full. The linters themselves need the same care: markdownlint takes `--dot`, per [[markdown-top-level-heading]].
