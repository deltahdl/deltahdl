#pragma once

#include "common/types.h"
#include "simulator/stmt_result.h"

namespace delta {

struct Expr;
struct Stmt;
class SimContext;
class Arena;

StmtResult ExecBlockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena);
StmtResult ExecNonblockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena);
StmtResult ExecExprStmtImpl(const Stmt* stmt, SimContext& ctx, Arena& arena);
StmtResult ExecVarDeclImpl(const Stmt* stmt, SimContext& ctx, Arena& arena);
StmtResult ExecForceOrAssignImpl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena);
StmtResult ExecReleaseOrDeassignImpl(const Stmt* stmt, SimContext& ctx);

// §10.4.1: Perform the LHS assignment portion of a blocking assign using a
// pre-evaluated RHS value (used by intra-assignment delay/event).
void PerformBlockingAssign(const Expr* lhs, const Logic4Vec& rhs_val,
                           SimContext& ctx, Arena& arena);

// §10.4.2: Schedule an NBA event with an optional time offset.
void ScheduleNonblockingAssign(const Stmt* stmt, const Logic4Vec& rhs_val,
                               uint64_t delay_ticks, SimContext& ctx,
                               Arena& arena);

}  // namespace delta
