Implement a single LRM subclause.

Arguments: $ARGUMENTS

Parse the arguments to extract:
- `--lrm <path>` (required) — path to the LRM PDF
- `--subclause <number>` (required) — subclause number (e.g., 4.1, 6.24.1, A.8.1)
- `--issue <number>` (required) — GitHub issue number to mark complete

## Steps

1. **Read the LRM PDF** at the `--lrm` path. Read the specified subclause. Also read:
   - Ancestor subclauses (e.g., for §6.24.1, read §6.24 and §6)
   - Any General or Overview sibling subclauses at each ancestry level

2. **Search the codebase** for existing related code before writing anything new.

3. **Implement using strict test-driven development.** For each requirement in the subclause:
   - Write a failing unit test first
   - Then write the implementation to make it pass
   - Cover all affected pipeline stages
   - Include error conditions and edge cases

4. **Mark complete.** After implementation, check off §{subclause} in Issue #{issue} on `deltahdl/deltahdl` using:
   ```
   gh api repos/deltahdl/deltahdl/issues/{issue} --jq ".body"
   ```
   Then update the body to change `- [ ] {subclause}` to `- [x] {subclause}` using:
   ```
   gh api repos/deltahdl/deltahdl/issues/{issue} -X PATCH --input -
   ```
   with a JSON payload `{"body": "<updated body>"}`.

## Constraints

- Do NOT copy or quote LRM prose into source code comments. Referencing section numbers and titles is fine.
- Do NOT build or run tests.
- Do NOT use `-j` or `--parallel` flags with `cmake --build`.
