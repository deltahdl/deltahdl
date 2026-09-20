#include "simulator/eval_class_array_handles.h"

#include <cstdint>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_assoc_class_handles.h"
#include "simulator/eval_class_array.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

// Whether the elements of the array property `ref` are class handles: the
// property's declared type names a class the simulation knows. A property of
// a class type has width_is_declared false and a 32-bit carrier for its
// width, so the type name is the one fact that tells a handle element from a
// value one.
bool ElementsAreHandles(const ClassArrayRef& ref, SimContext& ctx) {
  return !ref.prop->type_name.empty() &&
         ctx.FindClassType(ref.prop->type_name) != nullptr;
}

// `expr` as a single-index select, or null for an expression of any other
// shape.
const Expr* SingleIndexSelect(const Expr* expr) {
  if (expr == nullptr || expr->kind != ExprKind::kSelect ||
      expr->base == nullptr || expr->index == nullptr ||
      expr->index_end != nullptr) {
    return nullptr;
  }
  return expr;
}

}  // namespace

Logic4Vec ConstructElementObject(const Expr* rhs, std::string_view class_type,
                                 SimContext& ctx, Arena& arena) {
  if (rhs->lhs != nullptr && rhs->lhs->kind == ExprKind::kIdentifier) {
    auto* src = ctx.GetClassObject(EvalExpr(rhs->lhs, ctx, arena).ToUint64());
    if (src != nullptr) {
      return MakeLogic4VecVal(arena, 64,
                              ctx.AllocateClassObject(src->ShallowCopy(arena)));
    }
  }
  return EvalClassNew(class_type, rhs, ctx, arena, rhs->range.start);
}

bool TryClassArrayElementNewAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  const Expr* lhs = SingleIndexSelect(stmt->lhs);
  const Expr* rhs = stmt->rhs;
  if (lhs == nullptr || rhs == nullptr || rhs->kind != ExprKind::kCall ||
      rhs->text != "new") {
    return false;
  }
  ClassArrayRef ref;
  if (!ResolveClassArray(lhs->base, ctx, arena, ref) ||
      !ElementsAreHandles(ref, ctx)) {
    return false;
  }
  // §11.4.1: the index is evaluated once, before the constructor runs, which
  // may write the array itself.
  Logic4Vec idx_val = EvalExpr(lhs->index, ctx, arena);
  if (HasUnknownBits(idx_val)) return true;
  int64_t index = SelectBoundValue(idx_val);
  if (index < ref.lo || index >= ref.lo + static_cast<int64_t>(ref.size))
    return true;
  Logic4Vec handle =
      ConstructElementObject(rhs, ref.prop->type_name, ctx, arena);
  ref.obj->SetProperty(ClassArrayElementKey(ref.prop->name, index), handle);
  // §9.4.2: a change to an object's data member wakes a process waiting on
  // the object, as every other write to an element of the property tells it.
  ctx.NotifyClassHandleWatchers(ref.obj->handle);
  return true;
}

bool TryEvalClassArrayElementMember(const Expr* expr, SimContext& ctx,
                                    Arena& arena, Logic4Vec& out) {
  if (expr == nullptr || expr->kind != ExprKind::kMemberAccess ||
      expr->is_scope_resolution || expr->rhs == nullptr ||
      expr->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  const Expr* sel = SingleIndexSelect(expr->lhs);
  if (sel == nullptr) return false;
  ClassArrayRef ref;
  if (!ResolveClassArray(sel->base, ctx, arena, ref) ||
      !ElementsAreHandles(ref, ctx)) {
    return false;
  }
  // The element is read as any select of the property is (EvalSelect through
  // TryClassArrayElementSelect), an index addressing no element answering the
  // element type's default, which is the null handle.
  ClassObject* obj = ctx.GetClassObject(EvalExpr(sel, ctx, arena).ToUint64());
  if (obj == nullptr) return false;
  out = obj->GetProperty(expr->rhs->text, arena);
  return true;
}

bool TryEvalElementObjectMember(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  return TryEvalQueueElementMember(expr, ctx, arena, out) ||
         TryEvalClassArrayElementMember(expr, ctx, arena, out) ||
         TryEvalAssocElementMember(expr, ctx, arena, out);
}

}  // namespace delta
