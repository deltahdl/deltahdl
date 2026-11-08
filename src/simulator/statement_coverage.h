#pragma once

#include <functional>
#include <string>

#include "simulator/vpi_coverage.h"

namespace delta {

class CoverageControlState;
class SimContext;
struct RtlirDesign;
struct Stmt;

void ForEachCoverableStmt(const Stmt* stmt,
                          const std::function<void(const Stmt*)>& fn);

void AttachStatementCoverage(const RtlirDesign* design, SimContext& ctx);

void NoteStatementExecuted(const Stmt* stmt, SimContext& ctx);

EntityCoverage StatementHandleCoverage(const Stmt* stmt,
                                       const std::string& prefix,
                                       CoverageControlState& cov);

}  // namespace delta
