#include "simulator/eval_mailbox.h"

#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/awaiters.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_result.h"
#include "simulator/sync_objects.h"

namespace delta {

// §26.3 admits a package-qualified mailbox as the receiver, `p::mbx.get(x)`,
// found under the "p.mbx" key ExtractHandleMethodCallParts answers. This is
// asked of every call statement, so the method's name is matched before the
// key is made.
MailboxObject* MailboxCallTarget(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::string_view method) {
  if (!expr || expr->kind != ExprKind::kCall) return nullptr;
  const auto* access = expr->lhs;
  if (!access || access->kind != ExprKind::kMemberAccess) return nullptr;
  if (!access->rhs || access->rhs->text != method) return nullptr;
  MethodCallParts parts;
  if (!ExtractHandleMethodCallParts(expr, arena, parts)) return nullptr;
  return ctx.FindMailbox(parts.var_name);
}

int32_t MailboxBoundArg(const Expr* new_expr, SimContext& ctx, Arena& arena) {
  if (new_expr->args.empty() || !new_expr->args[0]) return 0;
  auto val = EvalExpr(new_expr->args[0], ctx, arena);
  return static_cast<int32_t>(static_cast<uint32_t>(val.ToUint64()));
}

// §15.4.3 and §15.4.4: the message put() or try_put() places, any singular
// expression, an object handle among them, held as the words of its value.
static uint64_t MailboxMessageArg(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  if (expr->args.empty() || !expr->args[0]) return 0;
  return EvalExpr(expr->args[0], ctx, arena).ToUint64();
}

// §15.4.5 through §15.4.8: the message a retrieval or a copy hands out goes
// to the variable the call's one argument names, a valid left-hand
// expression, sized to it as an assignment sizes its value.
static void StoreMailboxMessage(const Expr* expr, uint64_t msg, SimContext& ctx,
                                Arena& arena) {
  if (expr->args.empty() || !expr->args[0]) return;
  PerformBlockingAssign(expr->args[0], MakeLogic4VecVal(arena, 64, msg), ctx,
                        arena);
}

// §15.4.6 and §15.4.8: try_get() removes the front message and try_peek()
// copies it, each answering 0 for an empty mailbox and a positive integer
// once the message has reached the variable. The type of the message is not
// tracked, so the negative answer for a message of another type is never
// given.
static Logic4Vec EvalMailboxTryRetrieve(MailboxObject& mbx, bool remove,
                                        const Expr* expr, SimContext& ctx,
                                        Arena& arena) {
  uint64_t msg = 0;
  int32_t got = remove ? mbx.TryGet(msg) : mbx.TryPeek(msg);
  if (got > 0) StoreMailboxMessage(expr, msg, ctx, arena);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(got));
}

bool TryEvalMailboxMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out) {
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "num")) {
    out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(mbx->Num()));
    return true;
  }
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "try_put")) {
    auto placed = mbx->TryPut(MailboxMessageArg(expr, ctx, arena));
    out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(placed));
    return true;
  }
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "try_get")) {
    out = EvalMailboxTryRetrieve(*mbx, true, expr, ctx, arena);
    return true;
  }
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "try_peek")) {
    out = EvalMailboxTryRetrieve(*mbx, false, expr, ctx, arena);
    return true;
  }
  return false;
}

bool TryMailboxNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall ||
      stmt->rhs->text != "new")
    return false;
  auto* mbx = ctx.FindMailbox(stmt->lhs->text);
  if (!mbx) return false;
  mbx->Build(MailboxBoundArg(stmt->rhs, ctx, arena));
  return true;
}

bool IsMailboxBlockingCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  return MailboxCallTarget(expr, ctx, arena, "put") != nullptr ||
         MailboxCallTarget(expr, ctx, arena, "get") != nullptr ||
         MailboxCallTarget(expr, ctx, arena, "peek") != nullptr;
}

// §15.4.3: the message is evaluated before the process may suspend, so a
// put() that waits for room stores the value its argument had when the call
// was reached. §15.4.5 and §15.4.7: the message get() or peek() waited for
// reaches the named variable once the wait ends, at the time of the put()
// that ended it.
ExecTask ExecMailboxCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "put")) {
    co_await MailboxPutAwaiter{*mbx, MailboxMessageArg(expr, ctx, arena)};
    co_return StmtResult::kDone;
  }
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "get")) {
    uint64_t msg = co_await MailboxGetAwaiter{*mbx};
    StoreMailboxMessage(expr, msg, ctx, arena);
    co_return StmtResult::kDone;
  }
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "peek")) {
    uint64_t msg = co_await MailboxPeekAwaiter{*mbx};
    StoreMailboxMessage(expr, msg, ctx, arena);
  }
  co_return StmtResult::kDone;
}

}  // namespace delta
