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
                      SimContext& ctx, Arena& arena);
void WriteBitSelect(Variable* var, const Expr* lhs, const Logic4Vec& rhs_val,
                    SimContext& ctx, Arena& arena);
Logic4Vec ResizeToWidth(Logic4Vec val, uint32_t target_width, Arena& arena);
bool TryArrayBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);
bool TryAssocIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena& arena);
bool TryQueueIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena& arena);
bool TryQueueBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

}  // namespace delta
