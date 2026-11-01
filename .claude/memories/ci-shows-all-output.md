---
name: ci-shows-all-output
description: "Every CI step shows all the output its processes produce; no quiet flags, no /dev/null, no captured output left unprinted"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 09c3f072-0966-45c7-8c54-f5eb71974e31
  modified: 2026-11-01T15:52:25.973Z
---

# CI shows all output

Every step of every workflow and composite action shows everything its tools print, for passing cases as well as failing ones. That means:

- no `-q`, `--quiet`, `--silent` or `--status` flags;
- no `>/dev/null`;
- `ctest --verbose`, not `--output-on-failure`;
- `git clone --progress`;
- `PYTHONUNBUFFERED=1`, so Python's output is not held back in a buffer;
- output that is captured, into a variable or file or by `subprocess.run(capture_output=True)`, is printed as well;
- when a tool reports only a total, such as `llvm-profdata merge`, which names none of its inputs, the step lists every item itself; a count line alone reads as a summary hiding the work.

A plain string test, such as `grep -q` on a value already in the log, hides nothing and can stay.

**Why:** the user wants to read a step's log without guessing what was left out. A step that printed nothing, or printed only when it failed, read to them as hidden output, whichever step it was.

**How to apply:** when writing or reviewing any CI step or runner script, show what it runs, and stream it rather than reporting at the end. Complements [[failing-loudly-in-orchestrators]] and [[composite-actions]].
