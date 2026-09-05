# Commit and docstring scope

When changing a shared module — `satisfy_subclause.oracles`, for example — stand the diff and the commit message on that module's own contract. Do not name a downstream caller's artifact inside the module's docstrings, comments, error messages or commit message, even when that caller is what surfaced the bug.

Commit `de576bda8` was flagged twice for this. First the message anchored the change in "the cross-chapter cycle in `docs/dependency_graph.json`"; then the docstring of `parse_dependencies` named the same file. Both treated one caller's symptom as the rationale, when the rule — that aggregate identifiers are not satisfiable subclauses — applies to every caller.

Before writing any of those, ask whether it would make sense to a reader who has never heard of anything that calls the module. If naming a downstream module is what makes the rationale work, put the rationale in the issue or in a cross-cutting document instead. The standard has the same shape: a clause that re-presents another subclause's production does not own its rules.
