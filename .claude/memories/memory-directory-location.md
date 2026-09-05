---
name: memory-directory-location
description: Memories belong in .claude/memories/ inside the repository; rules stay in .claude/rules/.
metadata:
  type: feedback
---

# Where rules and memories live

Write memories to `.claude/memories/` in this repository, with the index at `.claude/memories/MEMORY.md`, rather than to the per-project directory under `~/.claude/projects/`. Leave the standing conventions where they are, one note per topic under `.claude/rules/`, each linked from a section of `.claude/CLAUDE.md`.

**Why:** the user said so on 2026-09-05. Both directories are tracked in git, so a memory written there travels with the repository and is readable by anyone working in it, while the path under `~/.claude/projects/` is local to one machine and empty.

**How to apply:** a convention learned in a session still gets a section in `.claude/CLAUDE.md` and a note in `.claude/rules/`. Everything the memory format covers — who the user is, feedback on how to work, ongoing project state, external references — gets a file in `.claude/memories/` and a one-line pointer in `MEMORY.md` beside it. Open every file in the directory, `MEMORY.md` included, with a top-level heading under the frontmatter: the markdownlint job in `.github/workflows/documentation.yml` runs MD041 over `**/*.md` and goes red on a memory that starts with body text.
