---
name: per-line-coverage-from-ci-artifacts
description: "The assert-coverage log counts missed lines per file only; the lines themselves are read from the run's artifacts with a local llvm-cov."
metadata:
  node_type: memory
  type: reference
  originSessionId: db1b45f3-3ddb-419c-ae00-cf0b0b977fee
  modified: 2026-10-19T20:49:49.957Z
---

The assert-coverage job prints `llvm-cov report`, a missed-line count per
file, and names no line. When a push raises TOTAL and the file holding the
new misses is known, read the lines from the run's own artifacts rather than
guessing which branch went unrun:

1. Download the `coverage-simulator` artifact (the instrumented `deltahdl`
   and `libdeltahdl_lib.so`) and every `profdata-unit-shard-*` artifact of
   that run through `gh api repos/deltahdl/deltahdl/actions/artifacts/<id>/zip`
   into the scratchpad. Unit shards alone are about 20 MB; the sv-tests and
   e2e profraw artifacts run to gigabytes and are not needed for code only
   unit tests reach.
2. `llvm-profdata merge -sparse` the shards, then
   `llvm-cov export <deltahdl> -object <libdeltahdl_lib.so>
   -instr-profile=<merged> --format=lcov` and keep the `DA:<line>,0` records
   of the file's `SF:` block.
3. Read those line numbers against `git show <sha>:<path>`, the source as the
   run built it.

Homebrew's `/opt/homebrew/opt/llvm/bin` tools read the Linux objects. This is
reading CI's output, not a local build, so it sits within
[[verifying-through-ci]].

**Why:** a guess at the missed line cost a whole CI round more than once; the
report gives a count, and two plausible branches can share a file.

**How to apply:** reach for it as soon as a red coverage run's per-file diff
names a file and the missed line is not obvious from the change.
