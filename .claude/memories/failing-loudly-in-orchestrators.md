---
name: failing-loudly-in-orchestrators
description: Crash the run when something goes wrong inside an orchestrator under scripts/, rather than skipping the item and carrying on.
metadata:
  type: feedback
---

# Failing loudly in the orchestrator scripts

Crash the run when something goes wrong inside one of the orchestrators under `scripts/` — an oversize dependency cycle, an unexpected oracle result, a bad dependency — rather than skipping the failing item and carrying on.

**Why:** The user is the one running these orchestrators. Silent partial-success runs disguise failures, spend tokens on unrelated downstream work, and leave it ambiguous whether the run finished. A hard failure forces the question.

**How to apply:** Recording human-resolvable state first is fine and often desirable — label the issue, write the report file. The very next thing must be a raise, or an exit with a non-zero code. A plain `return` after a fatal condition is almost always wrong here. Reserve quiet returns for the genuinely fine no-op, such as `commit_mutator_result` in `scripts/satisfy_subclause/mutators.py` returning `False` on an empty diff, because the subclause was already satisfied.
