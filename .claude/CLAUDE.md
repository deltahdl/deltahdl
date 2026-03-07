# LRM PDFs

- **SV LRM** (IEEE 1800-2023 SystemVerilog): `~/Library/CloudStorage/GoogleDrive-jdrowne@10ulabs.com/Shared drives/10U Labs Shared Drive/Standards/SystemVerilog/LRM/1800-2023.pdf`
- **UVM LRM** (IEEE 18002-2020): `~/Library/CloudStorage/GoogleDrive-jdrowne@10ulabs.com/Shared drives/10U Labs Shared Drive/Standards/UVM/18002-2020.pdf`
- **1735 LRM** (IEEE 1735-2023): `~/Library/CloudStorage/GoogleDrive-jdrowne@10ulabs.com/Shared drives/10U Labs Shared Drive/Standards/IEEE 1735/1735-2023.pdf`

# Implementing LRM clauses

When asked to implement a clause or subclause:

1. **Read the PDF.** Read the relevant section from the LRM PDF, plus ancestor subclauses and any General/Overview siblings for context.
2. **Search the codebase** for existing related code before writing anything new.
3. **Strict TDD.** For each requirement: write a failing unit test first, then implement. Cover all affected pipeline stages. Include error conditions and edge cases.
4. **Do not copy LRM prose** into source comments. Referencing section numbers and titles is fine.
5. **Do not build or run tests.**
6. **Do not use `-j`** or `--parallel` with `cmake --build`.

## Implementing a full clause

When given a clause number, a clause issue, and a master issue:

1. Read the clause from the PDF. Discover **all** subclauses at every depth (e.g., 6.6, 6.6.1, 6.6.4.1). Determine which are implementable as software.
2. Sync a checklist on the clause issue with `- [ ] N.N Title` lines, nested by depth. Preserve already-checked items. Every leaf subclause gets its own checklist item.
3. For each unchecked subclause in order:
   a. Implement it (steps above). Each leaf subclause must be individually implemented and checked off — do not batch.
   b. Commit and push: `git add -A && git commit` with message `Implement §X.Y.Z` and trailer `Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>`. Skip if no changes.
   c. Check off the subclause in the clause issue.
4. When all done: close the clause issue, then mark the master issue table row (the one containing `#{clause-issue}`) with `:white_check_mark:` in the Status column.

## GitHub

- Repo is always `deltahdl/deltahdl`.
- Use `gh api repos/deltahdl/deltahdl/issues/{N}` for all issue operations.
