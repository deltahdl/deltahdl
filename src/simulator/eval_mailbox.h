#pragma once

#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "simulator/exec_task.h"

namespace delta {

class CallResultReceiverScope;
struct Expr;
struct MailboxObject;
struct Stmt;
class Arena;
class SimContext;

MailboxObject* MailboxCallTarget(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::string_view method);

int32_t MailboxBoundArg(const Expr* new_expr, SimContext& ctx, Arena& arena);

bool TryEvalMailboxMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out);

bool TryMailboxNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

bool IsMailboxBlockingCall(const Expr* expr, SimContext& ctx, Arena& arena);

bool TryExecMailboxCallInFunction(const Expr* expr, SimContext& ctx,
                                  Arena& arena);

ExecTask ExecMailboxCall(const Expr* expr, SimContext& ctx, Arena& arena,
                         CallResultReceiverScope& held);

}  // namespace delta
