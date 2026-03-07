Implement an entire LRM clause by discovering and implementing each subclause.

Arguments: $ARGUMENTS

Parse the arguments to extract:
- `--lrm <path>` (required) — path to the LRM PDF
- `--clause <number>` (required) — top-level clause number (e.g., 4, 22, A)
- `--clause-issue <number>` (required) — GitHub issue tracking this clause's subclauses
- `--master-issue <number>` (required) — GitHub master issue with the clause table

## Phase 1: Discover subclauses

1. **Read the clause** from the LRM PDF at the `--lrm` path. Identify all subclauses (direct and indirect).

2. **Determine implementability.** For each subclause, decide whether it describes functionality implementable as software (parsing, simulation, synthesis, elaboration, scheduling). Exclude purely informational or editorial subclauses.

3. **Sync the GitHub issue checklist.** Fetch the clause issue body:
   ```
   gh api repos/deltahdl/deltahdl/issues/{clause-issue} --jq ".body"
   ```
   Build or update a checklist in the issue body under a `## Subclauses` heading:
   ```
   - [ ] 4.1 General
   - [ ] 4.2 Overview
     - [ ] 4.2.1 Details
   ```
   Preserve any already-checked items (`- [x]`). Nest by depth (2 spaces per level relative to the shallowest). Update the issue:
   ```
   gh api repos/deltahdl/deltahdl/issues/{clause-issue} -X PATCH --input -
   ```
   with JSON payload `{"body": "<updated body>"}`.

## Phase 2: Implement subclauses

For each unchecked subclause in order:

1. **Read the subclause** from the LRM PDF. Also read ancestor subclauses and any General/Overview siblings for context.

2. **Search the codebase** for existing related code before writing anything new.

3. **Implement using strict test-driven development.** For each requirement:
   - Write a failing unit test first
   - Then write the implementation to make it pass
   - Cover all affected pipeline stages
   - Include error conditions and edge cases

4. **Commit and push:**
   ```
   git add -A
   git commit -m "Implement §{subclause}\n\nCo-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>"
   git push
   ```
   Skip the commit if there are no staged changes.

5. **Check off the subclause** in the clause issue. Fetch the body, change `- [ ] {subclause}` to `- [x] {subclause}`, and update.

6. **Repeat** for the next unchecked subclause.

## Phase 3: Close out

When all subclauses are checked:

1. **Close the clause issue:**
   ```
   gh api repos/deltahdl/deltahdl/issues/{clause-issue} -X PATCH -f state=closed
   ```

2. **Mark the master issue complete.** Fetch the master issue body:
   ```
   gh api repos/deltahdl/deltahdl/issues/{master-issue} --jq ".body"
   ```
   Find the table row containing `#{clause-issue}` and set its Status column to `:white_check_mark:`. Update the body.

## Constraints

- Do NOT copy or quote LRM prose into source code comments. Referencing section numbers and titles is fine.
- Do NOT build or run tests.
- Do NOT use `-j` or `--parallel` flags with `cmake --build`.
