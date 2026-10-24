---
name: new-struct-members-go-last
description: A member added to an AST struct goes after every member that tests and helpers brace-initialize by position; inserting it earlier shifts their lists and fails the build.
metadata:
  node_type: memory
  type: project
  originSessionId: a5d84b64-23c0-46eb-a35e-39d1190f4d81
  modified: 2026-10-24T11:57:42.729Z
---

# New struct members go last

Tests and test helpers under `test/` and `lib/cpp/` build AST structs such as `FunctionArg` with positional brace lists, `{Direction::kRef, false, false, false, {}, "v", nullptr, {}}`, naming the members in declaration order. A member inserted ahead of the last one those lists name shifts every value after it: the build fails across unit-test and clang-tidy shards at once.

**Why:** such a list names neither the struct nor its members, so a search for the struct's name misses it, and so does a pattern keyed on one argument shape.

**How to apply:** add the member at the end of the struct, after the members the lists name, with a default member initializer; clang does not report a positional list that leaves out a member with one. Before adding any member, grep `test/` and `lib/` for the first member's literal opening a brace list (for `FunctionArg`, `\{Direction::k`) to see how far the lists reach. See [[verifying-through-ci]].
