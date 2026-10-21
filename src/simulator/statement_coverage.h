#pragma once

// IEEE 1800-2023 §40.2.2 statement coverage: whether each statement has
// executed, and, as §40.2.2 lets an implementation offer and §40.5.2's
// vpiCoveredCount reads, how many times.

#include <functional>
#include <string>

#include "simulator/vpi_coverage.h"

namespace delta {

class CoverageControlState;
class SimContext;
struct RtlirDesign;
struct Stmt;

// §40.2.2 counts as a statement anything the standard defines as one. `stmt`
// and each statement it holds, in every place a statement nests in another,
// are handed to `fn`; a declaration a block holds is not a statement and is
// left out, and so are a for loop's initializations and steps, which A.6.8
// writes as assignments of its header rather than as statements.
void ForEachCoverableStmt(const Stmt* stmt,
                          const std::function<void(const Stmt*)>& fn);

// §40.2.2: count the statements of every instance's procedures, tasks and
// functions as its coverable statements, and collect them.
void AttachStatementCoverage(const RtlirDesign* design, SimContext& ctx);

// §40.2.2: `stmt` begins executing in the instance the running process stands
// in; it counts as executed once more there while the instance collects
// statement coverage.
void NoteStatementExecuted(const Stmt* stmt, SimContext& ctx);

// §40.5.2: the statements a statement handle stands for, in the instance
// keyed `prefix`: those a begin-end or fork-join block holds, and any other
// statement with those it holds; how many there are, how many have executed,
// and their executions summed.
EntityCoverage StatementHandleCoverage(const Stmt* stmt,
                                       const std::string& prefix,
                                       CoverageControlState& cov);

}  // namespace delta
