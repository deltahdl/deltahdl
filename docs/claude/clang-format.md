# Formatting with clang-format

Always run `clang-format -i --style=google` on every file a change touches. This is the one local tool the repository allows, and the reason is the `-i`: it rewrites the file, so running it is how the committed bytes come to exist. Every other gate only judges what is already there, and judging belongs to CI — see [verifying-through-ci](verifying-through-ci.md).

The repository has no `.clang-format` file, so a bare `clang-format -i` falls back to LLVM style and reformats the entire file — splitting `if`/`return`, changing switch indentation — producing a large spurious diff that buries the real change and fails the gate. CI checks with `clang-format --dry-run --Werror --style=google`.

If the style flag is missed, `git checkout` the files, re-apply the edits, and re-format with the flag. Do not then run the `--dry-run --Werror` form to confirm: that is the judging half, it is a CI job, and `-i` has already written whatever it would report. Note that the formatting gate runs across all of `src/` and `test/`, so it stays red on pre-existing violations regardless of the change in hand.
