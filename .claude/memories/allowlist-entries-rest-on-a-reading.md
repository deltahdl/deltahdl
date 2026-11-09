---
name: allowlist-entries-rest-on-a-reading
description: "A name joins one of the two allowlists under etc/ only for the one kind of reason that list admits, and the reading that shows it goes in the commit message that adds the line, never in the list."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 71fdefb1-3397-48b8-838f-7c5e17be7223
  modified: 2026-11-08T03:42:51.187Z
---

# What an allowlist entry rests on

Two lists under `etc/` let a job in `.github/workflows/deltahdl.yml` pass a name it would otherwise refuse. Each admits one kind of reason, and nothing else:

- **`etc/test_only_accessor_allowlist.txt`**, read by `assert-no-test-only-accessors`, which reports an accessor under `src/` that hands back a container and that only tests call. An accessor is listed only when production reads the member it returns directly, so the accessor is a spare window for tests, or when nothing reads the data and an open issue says what is to become of it. A record nothing reads, with no issue, is a defect to fix or file, not an entry.
- **`etc/elaborator_stmt_link_allowlist.txt`**, read by `assert-no-hand-written-stmt-link-lists`, which reports a file under `src/elaborator/` that names `then_branch`, `else_branch` or `for_body` itself. A file is listed only when its walk has to know which link a child came from, which `ForEachChildStmt` does not say, or when it is `src/elaborator/elaborator_validate_internal.h`, where the links are walked for every other caller.

An entry is the bare line, `NAME HEADER` in the first list and a path in the second, with no comment beside it, per [no-comments-in-any-file](no-comments-in-any-file.md).

**Why:** A reason written beside an entry cites line numbers and issues that move as the code changes, and no job reads it, so it goes stale unseen. A commit message stays fixed to the change that made the reason true.

**How to apply:** Before adding a line, read the code that justifies it: print the production lines that read the member, or the lines of the walk that tell one link from another, or find the open issue. Give that reading in the commit message that adds the line, citing file and line. For a filed defect, the issue names the entry and says to delete it in the commit that fixes the defect. Each job also fails on a listed name it no longer reports, so the change that makes an entry unnecessary deletes it in the same commit.
