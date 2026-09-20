#include "simulator/eval_call_result.h"

#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

// Whether `side`, the handle side of a member access, is a method call or a
// member path down from one, `f()` or `f().p.q`: the object it denotes is the
// one the call returned, which no name resolves. A path from a name is left to
// the resolvers that own it, and a select on the way to the element paths.
bool RootedAtCall(const Expr* side) {
  if (side == nullptr) return false;
  if (side->kind == ExprKind::kCall) return true;
  return side->kind == ExprKind::kMemberAccess && !side->is_scope_resolution &&
         side->rhs != nullptr && side->rhs->kind == ExprKind::kIdentifier &&
         RootedAtCall(side->lhs);
}

// Whether `expr` selects a named member, `.m`, of something RootedAtCall.
bool SelectsMemberOfCallResult(const Expr* expr) {
  return expr != nullptr && expr->kind == ExprKind::kMemberAccess &&
         !expr->is_scope_resolution && expr->rhs != nullptr &&
         expr->rhs->kind == ExprKind::kIdentifier && RootedAtCall(expr->lhs);
}

// The object the handle `side` evaluates to, running the call it starts at;
// null where the result is the null handle.
ClassObject* CallResultObject(const Expr* side, SimContext& ctx, Arena& arena) {
  return ctx.GetClassObject(EvalExpr(side, ctx, arena).ToUint64());
}

// The method `name` of `obj` by the object's own type: a virtual one through
// the vtable (§8.20), else the one the class or a base of it declares.
ModuleItem* ResolveMethodOnObject(const ClassObject* obj, std::string_view name,
                                  const ClassTypeInfo** owner) {
  ModuleItem* method = obj->ResolveVirtualMethod(name, owner);
  if (method == nullptr)
    method = obj->ResolveMethodForType(name, obj->type, owner);
  return method;
}

}  // namespace

bool TryEvalCallResultMember(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out) {
  if (!SelectsMemberOfCallResult(expr)) return false;
  ClassObject* obj = CallResultObject(expr->lhs, ctx, arena);
  if (obj == nullptr) return false;
  out = obj->GetProperty(expr->rhs->text, arena);
  return true;
}

bool TryEvalCallResultMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  if (expr == nullptr || expr->kind != ExprKind::kCall ||
      !SelectsMemberOfCallResult(expr->lhs)) {
    return false;
  }
  const Expr* access = expr->lhs;
  InstanceMethodInfo info;
  info.obj = CallResultObject(access->lhs, ctx, arena);
  if (info.obj == nullptr) return false;
  info.method = ResolveMethodOnObject(info.obj, access->rhs->text, &info.owner);
  if (info.method == nullptr) return false;
  // Run as a method called through a variable is: a static one in class scope
  // (§8.10), an instance one with its defining class as the enclosing scope
  // (§8.15).
  out = RunInstanceMethod(info, expr, ctx, arena);
  return true;
}

}  // namespace delta
