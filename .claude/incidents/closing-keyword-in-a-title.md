---
name: closing-keyword-in-a-title
description: A commit title reading `Fix <script>'s implementability gate (#N)` closed the issue on push and it had to be reopened.
metadata:
  type: project
---

# The title that closed an issue

A commit titled `Fix <script>'s implementability gate (#N)` was written to name the bug being worked on, not to finish it. The brackets did not disable the keyword: GitHub read it as `fix #N` and closed the issue on push, before the verification run had happened, and it had to be reopened. The close and the reopen twelve minutes later are both still in that issue's timeline.

Supports [issue-closing-keywords](../rules/issue-closing-keywords.md).
