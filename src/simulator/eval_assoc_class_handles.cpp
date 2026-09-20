#include "simulator/eval_assoc_class_handles.h"

#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_class_array_handles.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

namespace {

// The declared associative array of class handles `sel` selects an element
// of, with its declared element class in `class_type`; null where `sel` is no
// single-index select, its base no bare name of a declared associative array,
// or the array's element type no class the simulation knows. The lowering
// records the element class under the array's name (SetVariableClassType in
// Lowerer::LowerVar) as it does for a variable of a class type, so the name
// is what tells an array of handles from one of values.
AssocArrayObject* HandleArrayOfSelect(const Expr* sel, SimContext& ctx,
                                      std::string_view& class_type) {
  if (sel == nullptr || sel->kind != ExprKind::kSelect ||
      sel->base == nullptr || sel->index == nullptr ||
      sel->index_end != nullptr || sel->base->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  AssocArrayObject* aa = ctx.FindAssocArray(sel->base->text);
  if (aa == nullptr) return nullptr;
  class_type = ctx.GetVariableClassType(sel->base->text);
  if (class_type.empty() || ctx.FindClassType(class_type) == nullptr)
    return nullptr;
  return aa;
}

// The object the element `sel` of a declared associative array of handles
// refers to, read as any select of the array is (EvalSelect, a key the array
// holds no entry under answering the element type's default, which is the
// null handle); null for a null handle.
ClassObject* ElementObject(const Expr* sel, SimContext& ctx, Arena& arena) {
  return ctx.GetClassObject(EvalExpr(sel, ctx, arena).ToUint64());
}

// `expr` as a member access `<select>.name` that is no scope resolution, with
// the select in `sel`; false for any other shape.
bool SplitMemberOfSelect(const Expr* expr, const Expr*& sel) {
  if (expr == nullptr || expr->kind != ExprKind::kMemberAccess ||
      expr->is_scope_resolution || expr->lhs == nullptr ||
      expr->rhs == nullptr || expr->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  sel = expr->lhs;
  return true;
}

// §7.8.1/§7.8.2: the entry of `aa` the evaluated index `idx` keys, written
// with `handle`, allocated where the array held none under the key.
void StoreElement(AssocArrayObject* aa, const Logic4Vec& idx,
                  const Logic4Vec& handle) {
  if (aa->is_string_key) {
    aa->str_data[AssocStringKey(idx)] = handle;
    return;
  }
  aa->int_data[AssocIntKey(idx, aa->is_wildcard, aa->index_width,
                           aa->is_index_signed)] = handle;
}

}  // namespace

bool TryAssocElementNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  const Expr* lhs = stmt->lhs;
  const Expr* rhs = stmt->rhs;
  if (rhs == nullptr || rhs->kind != ExprKind::kCall || rhs->text != "new")
    return false;
  std::string_view class_type;
  AssocArrayObject* aa = HandleArrayOfSelect(lhs, ctx, class_type);
  if (aa == nullptr) return false;
  // The index is evaluated once, before the constructor runs, which may write
  // the array itself.
  Logic4Vec idx = EvalExpr(lhs->index, ctx, arena);
  // §7.8.6: an integral index carrying an x or z bit is invalid, and a write
  // through one is a no-op.
  if (!aa->is_string_key && HasUnknownBits(idx)) return true;
  Logic4Vec handle = ConstructElementObject(rhs, class_type, ctx, arena);
  StoreElement(aa, idx, handle);
  // §9.4.2: a change to an aggregate element wakes a process waiting on the
  // array, as every other write to an element of it tells the watchers armed
  // on the variable under its name.
  NotifyOwningVar(ctx, lhs->base->text);
  return true;
}

bool TryEvalAssocElementMember(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  const Expr* sel = nullptr;
  std::string_view class_type;
  if (!SplitMemberOfSelect(expr, sel) ||
      HandleArrayOfSelect(sel, ctx, class_type) == nullptr) {
    return false;
  }
  ClassObject* obj = ElementObject(sel, ctx, arena);
  if (obj == nullptr) return false;
  out = obj->GetProperty(expr->rhs->text, arena);
  return true;
}

bool TryEvalAssocElementMethodCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  const Expr* sel = nullptr;
  std::string_view class_type;
  if (expr == nullptr || expr->kind != ExprKind::kCall ||
      !SplitMemberOfSelect(expr->lhs, sel)) {
    return false;
  }
  // §8.6 (printed page 183): an element of a declared array or of a queue is
  // as much a handle to call through as an associative array's, and had no
  // dispatch of its own.
  if (HandleArrayOfSelect(sel, ctx, class_type) == nullptr)
    return TryEvalElementObjectMethodCall(expr, ctx, arena, out);
  InstanceMethodInfo info;
  if (!ResolveMethodByDeclaredClass(ElementObject(sel, ctx, arena), class_type,
                                    expr->lhs->rhs->text, ctx, info)) {
    return false;
  }
  out = RunInstanceMethod(info, expr, ctx, arena);
  return true;
}

}  // namespace delta
