---
name: no-local-paths-in-code-or-workflows
description: "Code, tests, scripts and workflows name the standard as \"IEEE 1800-2023\", never by the local path `~/IEEE 1800-2023.pdf`; only .claude/ (skills and memories) names the path."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 0855f33b-6bae-425b-b28f-5541e226dc4a
  modified: 2026-09-21T13:01:45.656Z
---

# No local paths in code or workflows

A comment in `src/` or `test/`, a message in a workflow, a script's note and a test's argument name the standard as `IEEE 1800-2023` (a printed page is "printed page 125 of IEEE 1800-2023"). The path `~/IEEE 1800-2023.pdf` is written only under `.claude/` — the skills and the memories, which are what tell a session where the file is ([lrm-source-of-truth](lrm-source-of-truth.md)).

**Why:** The path is a symbolic link on one machine. The user said on 2026-09-21 that code and workflows should not refer to it because it is local, exempting the skills and then the memories; a reader of the repository has the standard by its name, not by a file in someone's home directory.

**How to apply:** Cite a page as "printed page N of IEEE 1800-2023". A snippet that needs the file takes its path from the environment (`os.environ["LRM"]`) rather than writing one in. A test that needs a PDF path passes a plain file name such as `"1800-2023.pdf"`.
