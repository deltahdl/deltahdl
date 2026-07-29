#pragma once

#include <string>

#include "common/types.h"
#include "simulator/stmt_result.h"

namespace delta {

struct Expr;
struct Stmt;
struct Variable;
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
StmtResult ExecReleaseOrDeassignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena);

void PerformBlockingAssign(const Expr* lhs, const Logic4Vec& rhs_val,
                           SimContext& ctx, Arena& arena);

void ScheduleNonblockingAssign(const Stmt* stmt, const Logic4Vec& rhs_val,
                               uint64_t delay_ticks, SimContext& ctx,
                               Arena& arena);

void BuildLhsName(const Expr* expr, std::string& out);
Variable* TryResolveArrayElement(const Expr* lhs, SimContext& ctx);
bool BuildCompoundLhsName(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::string& name);
Variable* TryResolveCompoundElement(const Expr* lhs, SimContext& ctx,
                                    Arena& arena);
Variable* ResolveLhsVariable(const Expr* lhs, SimContext& ctx);
bool WriteStructField(const Expr* lhs, const Logic4Vec& rhs_val,
                      SimContext& ctx);
void WriteBitSelect(Variable* var, const Expr* lhs, const Logic4Vec& rhs_val,
                    SimContext& ctx, Arena& arena);
Logic4Vec ResizeToWidth(Logic4Vec val, uint32_t target_width, Arena& arena);
bool TryArrayBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);
bool TryAssocIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena& arena);
bool TryQueueIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena& arena);
bool TryQueueBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

// §8.4: handle a blocking assignment whose right-hand side is a `new` call and
// whose left-hand side names a variable of a class type -- the two-step form
// `P p; p = new;` by which an object is created and its handle stored. `new`
// names a construction rather than a value to be read, so an assignment of
// this shape cannot be served by evaluating the right-hand side; it is
// recognized here, the object is created, and the handle is written to the
// target. Declines (returning false) for any other assignment, including one
// to a variable with no known class type, leaving it to the ordinary paths.
bool TryClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

}  // namespace delta
