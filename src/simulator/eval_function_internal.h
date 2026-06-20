#pragma once

#include <iosfwd>
#include <string_view>

#include "common/types.h"

namespace delta {

struct Expr;
struct ModuleItem;
class SimContext;
class Arena;

// Shared between eval_system_task.cpp and eval_system_func.cpp. The system-task
// helpers are defined once in eval_system_task.cpp; the system-function
// dispatch in eval_system_func.cpp routes to them.
Logic4Vec EvalPrngCall(const Expr* expr, SimContext& ctx, Arena& arena,
                       std::string_view name);
bool IsDisplayOrWriteTask(std::string_view name);
void ExecDisplayWrite(const Expr* expr, SimContext& ctx, Arena& arena);
void ExecSeverityTask(const Expr* expr, SimContext& ctx, Arena& arena,
                      const char* prefix, std::ostream& os);
Logic4Vec EvalDeferredPrint(const Expr* expr, SimContext& ctx, Arena& arena);
bool IsStrobeTask(std::string_view name);
bool IsMonitorTask(std::string_view name);
Logic4Vec EvalMonitor(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalMonitorFlag(SimContext& ctx, Arena& arena, std::string_view name);
Logic4Vec EvalVcdSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                         std::string_view name);

// Shared between eval_function_args.cpp and eval_function.cpp. The subroutine
// argument-binding and body-execution helpers are defined once in
// eval_function_args.cpp; the call-dispatch entry points in eval_function.cpp
// invoke them.
struct Variable;
void BindFunctionArgs(const ModuleItem* func, const Expr* expr, SimContext& ctx,
                      Arena& arena);
void WritebackOutputArgs(const ModuleItem* func, const Expr* expr,
                         SimContext& ctx, Arena& arena);
void ExecFunctionBody(const ModuleItem* func, Variable* ret_var,
                      SimContext& ctx, Arena& arena);
void WritebackQueueRefs(SimContext& ctx);
void WritebackAssocRefs(SimContext& ctx);

}  // namespace delta
