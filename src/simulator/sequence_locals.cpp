#include "simulator/sequence_locals.h"

#include <cstdint>
#include <cstdlib>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_exec.h"
#include "simulator/variable.h"

namespace delta {

uint32_t LocalWidth(TokenKind type_kw) {
  switch (type_kw) {
    case TokenKind::kKwByte:
      return 8;
    case TokenKind::kKwShortint:
      return 16;
    case TokenKind::kKwInt:
    case TokenKind::kKwInteger:
      return 32;
    case TokenKind::kKwLongint:
      return 64;
    default:
      return 1;
  }
}

uint32_t LocalWidth(const SeqLocalDecl& decl, SimContext& ctx, Arena& arena) {
  if (decl.packed_dims.empty()) return LocalWidth(decl.type_kw);
  uint32_t width = 1;
  for (const auto& [left, right] : decl.packed_dims) {
    const int64_t kLeft = SelectBoundValue(EvalExpr(left, ctx, arena));
    const int64_t kRight = SelectBoundValue(EvalExpr(right, ctx, arena));
    width *= static_cast<uint32_t>(std::abs(kLeft - kRight) + 1);
  }
  return width;
}

bool LocalIs4State(TokenKind type_kw) {
  return type_kw == TokenKind::kKwLogic || type_kw == TokenKind::kKwReg ||
         type_kw == TokenKind::kKwInteger;
}

// §16.10: the initialization assignments are performed in the order the
// locals are declared, one's expression reading the locals declared before
// it as assigned, so each is stood up in a scope of its own as its value is
// found; a local without an initialization is unassigned, x for a 4-state
// type.
std::vector<Logic4Vec> InitialLocals(const std::vector<SeqLocalDecl>& decls,
                                     SimContext& ctx, Arena& arena) {
  std::vector<Logic4Vec> values;
  values.reserve(decls.size());
  ctx.PushScope();
  for (const SeqLocalDecl& decl : decls) {
    const uint32_t kWidth = LocalWidth(decl, ctx, arena);
    Logic4Vec value = MakeLogic4Vec(arena, kWidth);
    if (decl.init != nullptr) {
      value = ResizeToWidth(OwnRhsWords(EvalExpr(decl.init, ctx, arena), arena),
                            kWidth, arena);
    } else if (LocalIs4State(decl.type_kw)) {
      FillWithX(value);
    }
    Variable* var = ctx.CreateLocalVariable(decl.name, value.width);
    var->is_4state = LocalIs4State(decl.type_kw);
    var->value = value;
    values.push_back(value);
  }
  ctx.PopScope();
  return values;
}

// §16.11: a subroutine call attached to a sequence is executed at each end
// point, in the Reactive region like an action block, and does not hold the
// evaluation up; an argument passed by value reads the sampled value the
// match was evaluated with, so each argument is evaluated here, the attempt's
// locals in scope, and its value stands in for the expression while the call
// runs.
void ScheduleMatchCall(const Expr* call, SimContext& ctx, Arena& arena) {
  std::vector<std::pair<const Expr*, Logic4Vec>> snaps;
  for (const Expr* arg : call->args) {
    if (arg != nullptr) snaps.emplace_back(arg, EvalExpr(arg, ctx, arena));
  }
  auto* ev = ctx.GetScheduler().GetEventPool().Acquire();
  ev->callback = [call, snaps = std::move(snaps), &ctx, &arena]() {
    for (const auto& snap : snaps) {
      ctx.SetDeferredArgSnapshot(snap.first, snap.second);
    }
    if (!TryExecSystemCallTask(call, ctx, arena)) EvalExpr(call, ctx, arena);
    for (const auto& snap : snaps) ctx.ClearDeferredArgSnapshot(snap.first);
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kReactive, ev);
}

}  // namespace delta
