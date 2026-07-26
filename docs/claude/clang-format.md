# Formatting with clang-format

Always run `clang-format -i --style=google`. The repository has no
`.clang-format` file, so a bare `clang-format -i` falls back to LLVM
style and reformats the entire file — splitting `if`/`return`, changing
switch indentation — producing a large spurious diff that buries the real
change and fails the gate. CI checks with
`clang-format --dry-run --Werror --style=google`.

If the style flag is missed, `git checkout` the files, re-apply the edits,
and re-format with the flag. Verify with the same `--dry-run --Werror`
command before committing. Note that the formatting gate runs across all
of `src/` and `test/`, so it stays red on pre-existing violations
regardless of the change in hand — check that your own files are clean.
