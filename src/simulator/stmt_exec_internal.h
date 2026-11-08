#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/types.h"
#include "simulator/exec_task.h"
#include "simulator/pattern_match.h"
#include "simulator/stmt_result.h"

namespace delta {

class CallResultReceiverScope;
struct Expr;
struct Stmt;
struct Logic4Vec;
class SimContext;
class Arena;

uint64_t DelayTicksFromValue(const Logic4Vec& val);

uint64_t DelayValueToTicks(const Logic4Vec& val, const SimContext& ctx);

uint64_t DelayValueToTicksIn(const Logic4Vec& val, const TimeScale& scale,
                             TimeUnit precision);

uint64_t DelayExprToTicks(const Expr* delay, SimContext& ctx, Arena& arena);

uint64_t DelayExprToTicksIn(const Expr* delay, const TimeScale& scale,
                            SimContext& ctx, Arena& arena);

const Stmt* SelectRandcaseBranch(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena);
ExecTask ExecRandcase(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecRandsequence(const Stmt* stmt, SimContext& ctx, Arena& arena);

struct Expr;
struct InstanceMethodInfo;
ExecTask ExecInstanceTaskCall(const InstanceMethodInfo& call, const Expr* expr,
                              SimContext& ctx, Arena& arena);
StmtResult ExecImmediateBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                       Arena& arena);

ExecTask ExecWait(const Stmt* stmt, SimContext& ctx, Arena& arena);
bool CurrentProcessEnded(const SimContext& ctx);
bool ProcessGoesOn(const SimContext& ctx);
StmtResult ExecDisableImpl(const Stmt* stmt, SimContext& ctx);
StmtResult ExecDisableForkImpl(SimContext& ctx);
bool IsSuspendingProcessCall(const Expr* expr, SimContext& ctx, Arena& arena);
ExecTask ExecSuspendingProcessCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, CallResultReceiverScope& held);
ExecTask ExecWaitOrder(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecCycleDelay(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecDelay(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecEventControl(const Stmt* stmt, SimContext& ctx, Arena& arena);

ExecTask ExecBlock(const Stmt* stmt, SimContext& ctx, Arena& arena);
std::string_view BindNamedBlockVariable(std::string_view name, SimContext& ctx);
std::string ActiveNamedScopePath(SimContext& ctx);
ExecTask ExecIf(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecCase(const Stmt* stmt, SimContext& ctx, Arena& arena);
struct CaseSelection {
  const Stmt* body = nullptr;
  std::vector<PatternBinding> bindings;
};
CaseSelection SelectCaseItem(const Stmt* stmt, SimContext& ctx, Arena& arena);
struct CaseLength {
  uint32_t width = 0;
  bool all_signed = true;
};
void IncludeInCaseLength(const Expr* e, SimContext& ctx, CaseLength& length);
Logic4Vec CaseOperandValue(const Expr* e, const CaseLength& length,
                           SimContext& ctx, Arena& arena);
bool CaseExactMatch(const Logic4Vec& sel, const Logic4Vec& pat);
ExecTask ExecFor(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecForeach(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecWhile(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecForever(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecRepeat(const Stmt* stmt, SimContext& ctx, Arena& arena);
std::optional<uint64_t> LoopIterationLimit(const Stmt* stmt, SimContext& ctx,
                                           Arena& arena);
uint64_t RepeatIterationCount(const Logic4Vec& count_val);
ExecTask ExecDoWhile(const Stmt* stmt, SimContext& ctx, Arena& arena);

ExecTask ExecImmediateAssert(const Stmt* stmt, SimContext& ctx, Arena& arena);
ExecTask ExecCheckerInstantiation(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena);
ExecTask ExecExpect(const Stmt* stmt, SimContext& ctx, Arena& arena);

void CollectExprAndStaticReads(const Expr* expr, SimContext& ctx,
                               std::unordered_set<std::string>& reads);

}  // namespace delta
