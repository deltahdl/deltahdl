# Positive phrasing in generated prompts

Prefer positive instructions to prohibitions when writing or editing the prompts this repository's scripts feed to a spawned session. Those are `build_lrm_read_instruction` and the step pipeline in `satisfy_subclause/mutators.py`, and the equivalents in `satisfy_clause`, `satisfy_clauses` and `satisfy_subclauses`.

Models follow "do X" more reliably than "don't do Y", because negation tends to surface the prohibited idea without suppressing it. The user pointed this out after a spawned session bypassed a "Read with the Read tool" hint and reached for `pypdf` through Bash.

Lead with the capability and how to use it — "The Read tool decodes PDFs natively; pass `pages: \"N\"` to read page N". Leave prohibitions to an enforcement layer, such as a PreToolUse hook or a disallowed-tools list. If a "don't" or "never" is being written into a prompt body, restate it as the action that is wanted instead.
