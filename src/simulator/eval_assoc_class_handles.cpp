#include "simulator/eval_assoc_class_handles.h"

#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_class_array_handles.h"
#include "simulator/eval_class_sync.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

namespace {

AssocArrayObject* HandleArrayOfSelect(const Expr* sel, SimContext& ctx,
                                      Arena& arena,
                                      std::string_view& class_type,
                                      ClassObject** owner = nullptr) {
  if (sel == nullptr || sel->kind != ExprKind::kSelect ||
      sel->base == nullptr || sel->index == nullptr ||
      sel->index_end != nullptr) {
    return nullptr;
  }
  AssocArrayObject* aa = FindAssocArrayOfBase(sel->base, ctx, arena, owner);
  if (aa == nullptr) return nullptr;
  class_type = aa->elem_class;
  if (class_type.empty() && sel->base->kind == ExprKind::kIdentifier)
    class_type = ctx.GetVariableClassType(sel->base->text);
  if (class_type.empty() ||
      (ctx.FindClassType(class_type) == nullptr &&
       BuiltinSyncKindOf(class_type, ctx) == SyncKind::kNone)) {
    return nullptr;
  }
  return aa;
}

ClassObject* ElementObject(const Expr* sel, SimContext& ctx, Arena& arena) {
  return ctx.GetClassObject(EvalExpr(sel, ctx, arena).ToUint64());
}

bool SplitMemberOfSelect(const Expr* expr, const Expr*& sel) {
  if (expr == nullptr || expr->kind != ExprKind::kMemberAccess ||
      expr->is_scope_resolution || expr->lhs == nullptr ||
      expr->rhs == nullptr || expr->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  sel = expr->lhs;
  return true;
}

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
  ClassObject* owner = nullptr;
  AssocArrayObject* aa =
      HandleArrayOfSelect(lhs, ctx, arena, class_type, &owner);
  if (aa == nullptr) return false;
  Logic4Vec idx = EvalExpr(lhs->index, ctx, arena);
  if (!aa->is_string_key && HasUnknownBits(idx)) return true;
  Logic4Vec handle = ConstructElementObject(rhs, class_type, ctx, arena);
  StoreElement(aa, idx, handle);
  if (owner != nullptr) {
    ctx.NotifyClassHandleWatchers(owner->handle);
  } else {
    NotifyOwningVar(ctx, lhs->base->text);
  }
  return true;
}

bool TryEvalAssocElementMember(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  const Expr* sel = nullptr;
  std::string_view class_type;
  if (!SplitMemberOfSelect(expr, sel) ||
      HandleArrayOfSelect(sel, ctx, arena, class_type) == nullptr) {
    return false;
  }
  ClassObject* obj = ElementObject(sel, ctx, arena);
  if (obj == nullptr) return false;
  out = obj->GetProperty(expr->rhs->text, arena);
  return true;
}

bool ResolveAssocElementMethod(const Expr* access, SimContext& ctx,
                               Arena& arena, InstanceMethodInfo& info,
                               bool report_null) {
  const Expr* sel = nullptr;
  std::string_view class_type;
  if (!SplitMemberOfSelect(access, sel) ||
      HandleArrayOfSelect(sel, ctx, arena, class_type) == nullptr) {
    return false;
  }
  ClassObject* obj = ElementObject(sel, ctx, arena);
  if (ResolveMethodByDeclaredClass(obj, class_type, access->rhs->text, ctx,
                                   info)) {
    return true;
  }
  if (obj == nullptr && report_null) {
    ReportNullHandleCall(access->rhs->text, access->rhs->range.start, ctx);
  }
  return false;
}

bool TryEvalAssocElementMethodCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  if (expr == nullptr || expr->kind != ExprKind::kCall) return false;
  InstanceMethodInfo info;
  if (!ResolveAssocElementMethod(expr->lhs, ctx, arena, info, true)) {
    return false;
  }
  out = RunInstanceMethod(info, expr, ctx, arena);
  return true;
}

}  // namespace delta
