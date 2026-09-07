---
name: markdown-top-level-heading
description: Open every Markdown file with a top-level heading; markdownlint MD041 runs across **/*.md including dot-directories.
metadata:
  type: project
---

# Every Markdown file opens with a top-level heading

Open every Markdown file with a top-level heading.

**Why:** The `markdownlint` job in `.github/workflows/documentation.yml` runs `markdownlint '**/*.md' --dot --disable MD013`, and MD041 requires the first line to be a top-level heading. The `--dot` is what puts `.claude/` in front of the linter, which markdownlint-cli would otherwise skip as a dot-prefixed directory, so the session notes are linted like anything else. YAML front matter is stripped before the check, so a memory file's `---` block does not count as the first line.

**How to apply:** Start the file with a single `#` heading, after the front matter where there is one. No configuration file can relax this: an `assert-no-linter-config-files` step fails the job on any markdownlint config, and `assert-no-inline-directives` fails it on any inline disable. MD013 is the only rule turned off, and that is done on the command line.
