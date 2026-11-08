#include "simulator/eval_class_array_handles.h"

#include <cstdint>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_assoc_class_handles.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_class_sync.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

namespace {

std::string_view ElementClassKey(const ClassArrayRef& ref, SimContext& ctx) {
  if (ref.static_owner != nullptr) return {};
  return PropertyClassName(ref.obj, ref.obj->type, ref.prop->name, ctx);
}

const Expr* SingleIndexSelect(const Expr* expr) {
  if (expr == nullptr || expr->kind != ExprKind::kSelect ||
      expr->base == nullptr || expr->index == nullptr ||
      expr->index_end != nullptr) {
    return nullptr;
  }
  return expr;
}

const Expr* SelectOfMemberAccess(const Expr* expr) {
  if (expr == nullptr || expr->kind != ExprKind::kMemberAccess ||
      expr->is_scope_resolution || expr->rhs == nullptr ||
      expr->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  return SingleIndexSelect(expr->lhs);
}

std::string_view DeclaredArrayElementClass(const Expr* base, SimContext& ctx) {
  std::string_view key;
  if (base->kind == ExprKind::kIdentifier) {
    key = base->text;
  } else if (base->kind == ExprKind::kMemberAccess &&
             base->is_scope_resolution) {
    key = ScopedOrBareTargetKey(base, ctx.GetArena());
  }
  if (key.empty() || ctx.FindArrayInfo(key) == nullptr) return {};
  std::string_view cls = ctx.GetVariableClassType(key);
  bool holds_handles = ctx.FindClassType(cls) != nullptr ||
                       BuiltinSyncKindOf(cls, ctx) != SyncKind::kNone;
  return holds_handles ? cls : std::string_view{};
}

bool TryDeclaredArrayElementNew(const Expr* lhs, const Expr* rhs,
                                SimContext& ctx, Arena& arena) {
  std::string_view cls = DeclaredArrayElementClass(lhs->base, ctx);
  if (cls.empty()) return false;
  Logic4Vec handle = ConstructElementObject(rhs, cls, ctx, arena);
  TrySelectBlockingAssign(lhs, handle, ctx, arena);
  return true;
}

bool ReadElementObjectProperty(const Expr* sel, std::string_view field,
                               SimContext& ctx, Arena& arena, Logic4Vec& out) {
  ClassObject* obj = ctx.GetClassObject(EvalExpr(sel, ctx, arena).ToUint64());
  if (obj == nullptr) return false;
  out = obj->GetProperty(field, arena);
  return true;
}

bool TryEvalDeclaredArrayElementMember(const Expr* expr, SimContext& ctx,
                                       Arena& arena, Logic4Vec& out) {
  const Expr* sel = SelectOfMemberAccess(expr);
  if (sel == nullptr || DeclaredArrayElementClass(sel->base, ctx).empty())
    return false;
  return ReadElementObjectProperty(sel, expr->rhs->text, ctx, arena, out);
}

}  // namespace

ClassObject* DeclaredArrayElementObject(const Expr* expr, SimContext& ctx,
                                        Arena& arena,
                                        const ClassTypeInfo*& declared) {
  const Expr* sel = SelectOfMemberAccess(expr);
  if (sel == nullptr) return nullptr;
  declared = ctx.FindClassType(DeclaredArrayElementClass(sel->base, ctx));
  if (declared == nullptr) return nullptr;
  return ctx.GetClassObject(EvalExpr(sel, ctx, arena).ToUint64());
}

Logic4Vec ConstructElementObject(const Expr* rhs, std::string_view class_type,
                                 SimContext& ctx, Arena& arena) {
  if (BuiltinSyncKindOf(class_type, ctx) != SyncKind::kNone) {
    return NewContainedSyncObject(rhs, class_type, ctx, arena);
  }
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
  if (TryDeclaredArrayElementNew(lhs, rhs, ctx, arena)) return true;
  ClassArrayRef ref;
  if (!ResolveClassArray(lhs->base, ctx, arena, ref)) return false;
  std::string_view class_key = ElementClassKey(ref, ctx);
  if (class_key.empty()) return false;
  Logic4Vec idx_val = EvalExpr(lhs->index, ctx, arena);
  if (HasUnknownBits(idx_val)) return true;
  int64_t index = SelectBoundValue(idx_val);
  if (index < ref.lo || index >= ref.lo + static_cast<int64_t>(ref.size))
    return true;
  Logic4Vec handle = ConstructElementObject(rhs, class_key, ctx, arena);
  ref.obj->SetProperty(ClassArrayRefElementKey(ref, index), handle);
  ctx.NotifyClassHandleWatchers(ref.obj->handle);
  return true;
}

bool TryEvalClassArrayElementMember(const Expr* expr, SimContext& ctx,
                                    Arena& arena, Logic4Vec& out) {
  const Expr* sel = SelectOfMemberAccess(expr);
  if (sel == nullptr) return false;
  ClassArrayRef ref;
  if (!ResolveClassArray(sel->base, ctx, arena, ref) ||
      ElementClassKey(ref, ctx).empty()) {
    return false;
  }
  return ReadElementObjectProperty(sel, expr->rhs->text, ctx, arena, out);
}

bool TryEvalElementObjectMember(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  return TryEvalQueueElementMember(expr, ctx, arena, out) ||
         TryEvalDeclaredArrayElementMember(expr, ctx, arena, out) ||
         TryEvalClassArrayElementMember(expr, ctx, arena, out) ||
         TryEvalAssocElementMember(expr, ctx, arena, out);
}

static bool SelectsAHandleElement(const Expr* sel, SimContext& ctx,
                                  Arena& arena, std::string_view& declared) {
  declared = DeclaredArrayElementClass(sel->base, ctx);
  if (!declared.empty()) return true;
  const QueueObject* q = FindQueueOfBase(sel->base, ctx, arena);
  if (q == nullptr || !q->holds_class_handles) return false;
  if (sel->base->kind == ExprKind::kIdentifier)
    declared = ctx.GetVariableClassType(sel->base->text);
  return true;
}

bool ResolveElementObjectMethod(const Expr* access, SimContext& ctx,
                                Arena& arena, InstanceMethodInfo& info,
                                bool report_null) {
  const Expr* sel = SelectOfMemberAccess(access);
  std::string_view declared;
  if (sel == nullptr || !SelectsAHandleElement(sel, ctx, arena, declared))
    return false;
  ClassObject* obj = ctx.GetClassObject(EvalExpr(sel, ctx, arena).ToUint64());
  if (ResolveMethodByDeclaredClass(obj, declared, access->rhs->text, ctx,
                                   info)) {
    return true;
  }
  if (obj == nullptr && report_null) {
    ReportNullHandleCall(access->rhs->text, access->rhs->range.start, ctx);
  }
  return false;
}

bool TryEvalElementObjectMethodCall(const Expr* expr, SimContext& ctx,
                                    Arena& arena, Logic4Vec& out) {
  if (expr == nullptr || expr->kind != ExprKind::kCall) return false;
  InstanceMethodInfo info;
  if (!ResolveElementObjectMethod(expr->lhs, ctx, arena, info, true)) {
    return false;
  }
  out = RunInstanceMethod(info, expr, ctx, arena);
  return true;
}

}  // namespace delta
