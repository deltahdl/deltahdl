---
name: no-comments-in-any-file
description: "No tracked file carries a comment or a docstring, in any language, apart from three exceptions; the reasoning goes in the commit message and the issue."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 71fdefb1-3397-48b8-838f-7c5e17be7223
  modified: 2026-11-08T03:42:44.505Z
---

# No comments in any file

No file deltahdl tracks carries a comment or a docstring. That covers every language in the tree: Python, YAML, the shell inside a workflow's or a composite action's `run:` steps, C, C++, CMake, shell scripts, SystemVerilog and Verilog, and the line-per-entry data files under `etc/` and `scripts/`. Only three kinds of comment stay:

- **Namespace end comments:** `clang-format --style=google` writes `}  // namespace NAME`, or `}  // namespace` for an anonymous namespace, on the brace that closes it, and writes it again when it is deleted.
- **The six annex headers** in `src/simulator/`, whose comments are the standard's text, per [[annex-files-are-not-edited]].
- **Test inputs whose comment is under test:** a SystemVerilog or Verilog input under `test/src/` whose test checks how a comment is handled, such as how comments lex or a directive written inside one. An input keeps its comments only when deleting one would change what its test asserts. The `--exclude` of the `assert-no-comments` job in `deltahdl.yml` lists exactly these inputs, each as a `*/test/src/…` glob, so an input that comes to need a comment is added to that list in the same commit, and every other input carries none. A test's own data goes in a sidecar beside its input rather than in a comment: an integration case under `test/src/integration/` names its `:subclause:`, `:stage:` and `:should_fail_because:` lines in `<stem>.metadata`, which `scripts/run_integration_tests` reads, failing the case on a line that names no known key.

**Why:** No compiler, test or linter checks prose beside code, so it stops being true and nothing says when. A rename leaves every sentence naming the old identifier wrong, in files the change never touched. The reasoning belongs in the commit message and the issue, which are dated and attached to a change. `git log -S '<a phrase>'` finds a deleted comment's text.

**How to apply:**

- Put the why in the commit message and the issue. An instruction to whoever edits a file next becomes a memory, per [[recording-what-a-session-learns]].
- In Python, a body that would hold only a docstring holds `pass`. A line that would carry `# pragma: no cover` gets a test instead: `runpy.run_module(..., run_name="__main__")` for a `__main__` guard, or `runpy.run_path` on a script package's `__main__.py` with `main` patched. The pylint jobs pass `--disable=missing-*-docstring` on the command line, since inline directives and configuration files are refused by their own gates.
- `assert-no-comments`, the 10U-Labs tool installed unpinned from PyPI, is the check. Its job in `.github/workflows/scripts.yml` reads `.claude/statusline.sh`, the only shell script tracked here, as well as that workflow, `lib/__init__.py`, `lib/python/`, `scripts/`, `test/lib/python/` and `test/scripts/`. Its job in `.github/workflows/deltahdl.yml` reads each entry of that workflow's `paths` filter, one for one, so a path added to the filter is added to the job's trees as well, per [[workflow-paths-name-the-programs-its-jobs-run]]. That job's `--exclude` names the six annex headers by file name and each input whose comment is under test by a `*/test/src/…` glob, and nothing else. The tool matches each glob with `fnmatch` against both the full path and the file name, and `*` there also matches `/`. The jobs in `jsonlint.yml` and `markdownlint.yml` read their own workflow file. The tool spares the namespace end comment itself. It picks a language by file extension alone, with no option to add one, so it reads no `.txt` file and no input with an extension of deltahdl's own, such as a `.vg` Verilog source or a `.bootstrap` file. It has no CMake reader either: 10U-Labs/assert-no-comments#11 closed as not planned, since the only `tree-sitter-cmake` on PyPI ships a Windows wheel alone.
- The three line-per-entry data files, `scripts/assert_subclause_citations/clauses.txt`, `etc/elaborator_stmt_link_allowlist.txt` and `etc/test_only_accessor_allowlist.txt`, hold one entry per line and nothing else: no `#` line, no blank line and no text after the entry. Their readers refuse any other line and name it. `known_subclauses` raises `ValueError`, and the `assert-no-hand-written-stmt-link-lists` and `assert-no-test-only-accessors` jobs in `deltahdl.yml` annotate the line. A data file added later gets a reader that refuses a stray line the same way, never one that skips it. Why an entry is there goes in the commit that adds it, per [[allowlist-entries-rest-on-a-reading]].
- The three CMake files, `CMakeLists.txt`, `src/CMakeLists.txt` and `test/CMakeLists.txt`, carry no comment, and neither do the e2e inputs written in a format that allows one but in a file the tool never reads, such as `test/src/e2e/library_map_predefined.files/adder.vg` and `test/src/e2e/bootstrap_entry_missing_library.bootstrap`. Their readers have to accept a comment, because CMake, Verilog and the Annex J.4.1 bootstrap format all allow one, so a comment added there is caught only by whoever reviews the change.

Related: [[module-terms-in-descriptions]], [[verifying-through-ci]].
