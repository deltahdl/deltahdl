#include <cstdint>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

// §6.24.2's $cast, moved out of eval_systask.cpp, which stood at the size the
// assert-no-oversized-source-files job fails at: the dynamic cast of a value
// into an enumeration, of a handle into a class variable, or of any other
// value into its destination, answering whether it took.

// §6.24.2: the cast succeeded, so the destination takes the value. A variable
// of the run's tables is written here; any other destination -- a class
// property named bare inside a method or through a handle (§8.3, §8.11) --
// is written as a blocking assignment to it writes it, since a property is
// held on its object and no variable of its name exists to find. Written by
// the name alone, `$cast(c, 1)` on a property `c` answered 1 and stored
// nothing.
static Logic4Vec CastAssignSuccess(const Expr* dest, uint64_t src_val,
                                   SimContext& ctx, Arena& arena) {
  auto* var = dest->kind == ExprKind::kIdentifier &&
                      NameDenotesVariable(dest->text, ctx)
                  ? ctx.FindVariable(dest->text)
                  : nullptr;
  if (var) {
    var->value = MakeLogic4VecVal(arena, var->value.width, src_val);
    // §9.4.2 again: §6.24.1's $cast has written a user variable.
    var->NotifyWatchers();
  } else {
    PerformBlockingAssign(dest, MakeLogic4VecVal(arena, 32, src_val), ctx,
                          arena);
  }
  return MakeLogic4VecVal(arena, 32, 1);
}

// §6.24.2: a destination of an enumeration type, wherever it is declared
// (EnumTypeOfExpr), takes the value when it is a member and is left as it was
// otherwise, the call answering whether it was.
static bool TryCastEnum(const Expr* dest, uint64_t src_val, SimContext& ctx,
                        Arena& arena, Logic4Vec& out) {
  const auto* enum_info = EnumTypeOfExpr(dest, ctx, arena);
  if (!enum_info) return false;
  for (const auto& m : enum_info->members) {
    if (m.value == src_val) {
      out = CastAssignSuccess(dest, src_val, ctx, arena);
      return true;
    }
  }
  out = MakeLogic4VecVal(arena, 32, 0);
  return true;
}

static bool AreCastCompatible(const ClassTypeInfo* a, const ClassTypeInfo* b) {
  return a->IsA(b) || b->IsA(a) || a->is_interface || b->is_interface;
}

// Static-type screen for a $cast to a class handle: if the source expression
// names a typed class variable whose declared type is not cast-compatible with
// the destination type, the cast fails outright.
static bool SrcClassTypeIncompatible(const Expr* src_expr,
                                     const ClassTypeInfo* dest_type,
                                     SimContext& ctx) {
  if (!src_expr || src_expr->kind != ExprKind::kIdentifier ||
      src_expr->text == "null") {
    return false;
  }
  auto src_class = ctx.GetVariableClassType(src_expr->text);
  if (src_class.empty()) return false;
  auto* src_type = ctx.FindClassType(src_class);
  return src_type && !AreCastCompatible(src_type, dest_type);
}

// §6.24.1 $cast: one dynamic cast request names a destination variable
// (dest_name) and the source it is cast from (its run-time handle src_val and
// the originating expression src_expr used for the static-type screen).
struct CastRequest {
  std::string_view dest_name;
  const Expr* dest;
  uint64_t src_val;
  const Expr* src_expr;
};

static bool TryCastClassHandle(const CastRequest& req, SimContext& ctx,
                               Arena& arena, Logic4Vec& out) {
  auto dest_class = ctx.GetVariableClassType(req.dest_name);
  if (dest_class.empty()) return false;
  auto* dest_type = ctx.FindClassType(dest_class);
  if (!dest_type) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }

  if (SrcClassTypeIncompatible(req.src_expr, dest_type, ctx)) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }

  if (req.src_val == kNullClassHandle) {
    out = CastAssignSuccess(req.dest, 0, ctx, arena);
    return true;
  }
  auto* src_obj = ctx.GetClassObject(req.src_val);
  if (!src_obj || !src_obj->type || !src_obj->type->IsA(dest_type)) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }
  out = CastAssignSuccess(req.dest, req.src_val, ctx, arena);
  return true;
}

Logic4Vec EvalCastSysFunc(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2 || !expr->args[0]) {
    return MakeLogic4VecVal(arena, 32, 0);
  }
  auto* dest_expr = expr->args[0];
  auto src = EvalExpr(expr->args[1], ctx, arena);
  uint64_t src_val = src.ToUint64();
  // §6.24.2: the destination is a variable or a class property, named bare or
  // through a handle; a class handle destination is screened by the class its
  // variable is declared with, which a bare name alone records.
  if (dest_expr->kind != ExprKind::kIdentifier &&
      dest_expr->kind != ExprKind::kMemberAccess) {
    return MakeLogic4VecVal(arena, 32, 0);
  }
  std::string_view dest_name = dest_expr->kind == ExprKind::kIdentifier
                                   ? dest_expr->text
                                   : std::string_view{};
  Logic4Vec out;
  if (TryCastEnum(dest_expr, src_val, ctx, arena, out)) return out;
  CastRequest cast_req{dest_name, dest_expr, src_val, expr->args[1]};
  if (TryCastClassHandle(cast_req, ctx, arena, out)) return out;
  return CastAssignSuccess(dest_expr, src_val, ctx, arena);
}

}  // namespace delta
