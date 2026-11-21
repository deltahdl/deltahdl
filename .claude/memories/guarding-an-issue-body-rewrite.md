---
name: guarding-an-issue-body-rewrite
description: "Rewriting an issue body by fetching it to a file, editing and `gh issue edit --body-file` must stop when the fetch fails; an empty file wipes the body. Prior versions come back through GraphQL userContentEdits."
metadata:
  node_type: memory
  type: feedback
  originSessionId: dbb14fe5-4f12-40b5-98ca-0948dad60b8a
  modified: 2026-11-21T02:52:35.421Z
---

# Guarding an issue body rewrite

When an issue body is rewritten by fetching it (`gh issue view --json body > file`), editing the file and writing it back with `gh issue edit --body-file`, chain every step with `&&` and check the file's size before the write. A failed fetch (GitHub answers HTTP 500 at times) leaves the redirect's file empty, and writing that back empties the issue.

**Why:** in a `;`-separated fetch, edit, write sequence, the write still runs after a failed fetch and replaces the body with nothing.

**How to apply:** `gh issue view N --json body --jq .body > f && python3 edit.py f && [ $(wc -c < f) -gt <old size> ] && gh issue edit N --body-file f`. A wiped body is recovered from the edit history: `gh api graphql -f query='query{repository(owner:"deltahdl",name:"deltahdl"){issue(number:N){userContentEdits(first:5){nodes{createdAt diff}}}}}'`, whose nodes run newest first and whose `diff` holds each version's full text. See [research-lives-in-issues](research-lives-in-issues.md).
