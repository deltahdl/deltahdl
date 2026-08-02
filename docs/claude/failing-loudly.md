# Failing loudly in pipeline code

Crash the run when something goes wrong inside a pipeline or orchestrator — an oversize dependency cycle, an unexpected oracle result, a bad dependency — rather than skipping the failing item and carrying on. Recording human-resolvable state first is fine and often desirable: label the issue, write the report file. The very next thing must be a raise, or an exit with a non-zero code. A plain `return` after a fatal condition is almost always wrong here.

The user is the one running these orchestrators. Silent partial-success runs disguise failures, spend tokens on unrelated downstream work, and leave it ambiguous whether the run finished. A hard failure forces the question. This was corrected on 2026-04-27, after the oversize-cycle handler was implemented with a quiet `return` so the orchestrator could continue to the next descendant.

Reserve quiet returns for the genuinely fine no-op, such as `commit_mutator_result` in `satisfy_subclause/mutators.py` returning `False` on an empty diff, because the subclause was already satisfied.
