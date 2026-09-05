# Positive phrasing in generated prompts

Prefer positive instructions to prohibitions when writing or editing the prompts this repository's scripts feed to a spawned session. Two functions build them: `build_lrm_read_instruction` in `lib/python/lrm/__init__.py`, and `build_steps` in `scripts/satisfy_subclause/mutators.py`. `scripts/satisfy_subclauses/pipeline.py` writes no prompts of its own, since it runs `python -m satisfy_subclause` as a subprocess.

Models follow "do X" more reliably than "don't do Y", because negation tends to surface the prohibited idea without suppressing it. [spawned-session-reached-for-pypdf](../memories/spawned-session-reached-for-pypdf.md) is the session that showed it.

Lead with the capability and how to use it — "The Read tool decodes PDFs natively; pass `pages: \"N\"` to read page N". Leave prohibitions to something that can enforce them, such as a PreToolUse hook or a disallowed-tools list. If a "don't" or "never" is being written into a prompt body, restate it as the action that is wanted instead.
