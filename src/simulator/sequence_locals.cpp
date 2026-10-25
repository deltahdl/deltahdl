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
#include "parser/ast_type.h"
#include "parser/expr_substitute.h"
#include "simulator/eval_function_internal.h"
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
    case TokenKind::kKwTime:
      return 64;
    default:
      return 1;
  }
}

uint32_t LocalWidth(const SeqLocalDecl& decl, SimContext& ctx, Arena& arena) {
  uint32_t width = 1;
  if (decl.named_type.kind == DataTypeKind::kNamed) {
    width = DeclaredTypeWidth(decl.named_type, ctx);
  } else if (decl.packed_dims.empty()) {
    return LocalWidth(decl.type_kw);
  }
  for (const auto& [left, right] : decl.packed_dims) {
    const int64_t kLeft = SelectBoundValue(EvalExpr(left, ctx, arena));
    const int64_t kRight = SelectBoundValue(EvalExpr(right, ctx, arena));
    width *= static_cast<uint32_t>(std::abs(kLeft - kRight) + 1);
  }
  return width;
}

bool LocalIs4State(TokenKind type_kw) {
  return type_kw == TokenKind::kKwLogic || type_kw == TokenKind::kKwReg ||
         type_kw == TokenKind::kKwInteger || type_kw == TokenKind::kKwTime;
}

// The keywords LocalWidth sizes wider than a bit, time aside, are the integer
// atom types Table 6-8 makes signed; time is unsigned.
bool LocalIsSigned(TokenKind type_kw) {
  return LocalWidth(type_kw) > 1 && type_kw != TokenKind::kKwTime;
}

bool LocalIs4State(const SeqLocalDecl& decl, const SimContext& ctx) {
  return decl.named_type.kind == DataTypeKind::kNamed
             ? DeclaredTypeIs4State(decl.named_type, ctx)
             : LocalIs4State(decl.type_kw);
}

bool LocalIsSigned(const SeqLocalDecl& decl, const SimContext& ctx) {
  if (decl.signing != TokenKind::kEof) {
    return decl.signing == TokenKind::kKwSigned;
  }
  return decl.named_type.kind == DataTypeKind::kNamed
             ? DeclaredTypeIsSigned(decl.named_type, ctx)
             : LocalIsSigned(decl.type_kw);
}

Variable* StandUpLocal(const SeqLocalDecl& decl, const Logic4Vec& value,
                       SimContext& ctx) {
  Variable* var = ctx.CreateLocalVariable(decl.name, value.width);
  var->is_4state = LocalIs4State(decl, ctx);
  var->is_signed = LocalIsSigned(decl, ctx);
  var->value = value;
  DataType type = decl.named_type;
  if (!decl.packed_dims.empty()) {
    type.packed_dim_left = decl.packed_dims.front().first;
    type.packed_dim_right = decl.packed_dims.front().second;
    type.extra_packed_dims.assign(decl.packed_dims.begin() + 1,
                                  decl.packed_dims.end());
  }
  RecordDeclaredRange(type, var, ctx, ctx.GetArena());
  // A type name written with dimensions after it stands for the element of
  // an array of it, which RecordDeclaredRange shaped, not the whole local.
  if (type.kind == DataTypeKind::kNamed && decl.packed_dims.empty()) {
    var->local_layout = NamedLayout(type, ctx);
  }
  return var;
}

void AssignMatchItemTarget(const SeqMatchAssign& item, Logic4Vec rhs,
                           Variable& local, SimContext& ctx, Arena& arena) {
  local.value = OwnRhsWords(local.value, arena);
  if (item.op != TokenKind::kEq) {
    rhs = EvalBinaryOp(CompoundAssignBaseOp(item.op),
                       EvalExpr(item.target, ctx, arena), rhs, arena);
  }
  PerformBlockingAssign(item.target, rhs, ctx, arena);
}

Logic4Vec AssignedLocalValue(const SeqMatchAssign& item, const Logic4Vec& whole,
                             Logic4Vec rhs, SimContext& ctx, Arena& arena) {
  if (item.target != nullptr) {
    ctx.PushScope();
    Variable* local = ctx.CreateLocalVariable(item.lvar, whole.width);
    local->value = whole;
    AssignMatchItemTarget(item, rhs, *local, ctx, arena);
    Logic4Vec value = local->value;
    ctx.PopScope();
    return value;
  }
  if (item.op != TokenKind::kEq) {
    rhs = EvalBinaryOp(CompoundAssignBaseOp(item.op), whole, rhs, arena);
  }
  return ResizeToWidth(OwnRhsWords(rhs, arena), whole.width, arena);
}

Expr* SubstituteTarget(const SeqMatchAssign& item, bool keeps_local,
                       const ActualsByFormal& actuals, Arena& arena) {
  if (item.target == nullptr) return nullptr;
  if (!keeps_local) return SubstituteFormals(item.target, actuals, arena);
  ActualsByFormal others = actuals;
  others.erase(item.lvar);
  return SubstituteFormals(item.target, others, arena);
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
    bool is_4state = LocalIs4State(decl, ctx);
    Logic4Vec value = MakeLogic4Vec(arena, kWidth);
    if (decl.init != nullptr) {
      value = ResizeToWidth(OwnRhsWords(EvalExpr(decl.init, ctx, arena), arena),
                            kWidth, arena);
      // §16.10 makes the initialization an assignment to the local, and
      // §6.11.2 has one to a 2-state variable turn x and z bits to 0.
      if (!is_4state) CoerceTo2State(value);
    } else if (is_4state) {
      FillWithX(value);
    }
    StandUpLocal(decl, value, ctx);
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
