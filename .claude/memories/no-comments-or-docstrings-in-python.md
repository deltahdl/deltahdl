---
name: no-comments-or-docstrings-in-python
description: The Python and YAML that scripts.yml covers carry no comments and no docstrings; the reasoning goes in the commit message.
metadata:
  type: feedback
---

# No comments or docstrings in the Python trees

Write no `#` comment and no docstring under `lib/python/`, `scripts/`, `test/lib/python/`, `test/scripts/` or in `.github/workflows/scripts.yml`.

**Why:** The `assert-no-comments` job in `.github/workflows/scripts.yml` (the 10U-Labs tool of that name) refuses every one of them, including a module, class or function docstring and a trailing `# pragma: no cover`. Prose beside code is checked by nothing and goes stale silently; the reasoning belongs in the commit message and the issue, which are dated and attached to a change. The pylint jobs pass `--disable=missing-*-docstring` on the command line for this reason, since inline directives and configuration files are refused by their own gates.

**How to apply:** Put the why in the commit subject and the issue. A body that would have held only a docstring holds `pass`. A line that would have carried `# pragma: no cover` gets a test instead: `runpy.run_module(..., run_name="__main__")` for a `__main__` guard, `runpy.run_path` on the `__main__.py` with `main` patched for a script package. Related: [[module-terms-in-descriptions]], [[verifying-through-ci]].
