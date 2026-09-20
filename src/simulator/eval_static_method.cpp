#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

// §8.10: run a static method with its class in scope but no `this`. Class scope
// makes unqualified references to the class's static methods/properties resolve
// to the single shared copy (see EvalIdentifier / ExecFuncIdentifierAssign).
// target.param_cls doubles as the scope class (as for the parameterized
// class-scope path), so a parameterized static method's return width resolves.
void RunStaticMethodInClassScope(ClassMethodTarget target, const Expr* expr,
                                 SimContext& ctx, Arena& arena,
                                 Logic4Vec& out) {
  ctx.PushScope();
  ctx.PushMethodClass(target.param_cls);
  ExecClassMethod(target, expr, ctx, arena, out);
  // §13.5.2: copy output/inout arguments back to the caller on return.
  WritebackOutputArgs(target.method, expr, ctx, arena);
  ctx.PopMethodClass();
  ctx.PopScope();
}

bool TryEvalEnclosingStaticCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  const ClassTypeInfo* cls = ctx.CurrentMethodClass();
  if (!cls) return false;
  auto it = cls->methods.find(std::string(expr->callee));
  if (it == cls->methods.end() || !it->second->is_static_method) return false;
  RunStaticMethodInClassScope({it->second, cls}, expr, ctx, arena, out);
  return true;
}

// §8.13: a subclass "inherits the members of the base class", and §8.6 makes a
// method one of those members. A call written with no receiver inside a class
// method therefore names a method of the enclosing class or of any class it
// inherits from, invoked on the object the enclosing method is already running
// on -- the receiver is implicit, not absent.
//
// Resolution starts at the object's dynamic type through the vtable, so an
// unqualified call to a virtual method reaches the override, and falls back to
// a walk from the lexically enclosing class up its base chain for a method that
// is not virtual. That is the same two-step the receiver-qualified path uses.
//
// The enclosing-class static call above is tried first and searches only that
// one class, so a static method inherited from a base reaches here; it is run
// in class scope rather than on `this`, because §8.10 gives a static method no
// `this` however it was named.
bool TryEvalEnclosingInstanceCall(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (ExtractMethodCallParts(expr, parts)) return false;
  if (expr->callee.empty()) return false;
  ClassObject* self = ctx.CurrentThis();
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  if (!self || !enclosing) return false;

  const ClassTypeInfo* defining = nullptr;
  ModuleItem* method = self->ResolveVirtualMethod(expr->callee, &defining);
  if (!method)
    method = self->ResolveMethodForType(expr->callee, enclosing, &defining);
  if (!method) return false;

  if (method->is_static_method) {
    RunStaticMethodInClassScope({method, defining}, expr, ctx, arena, out);
    return true;
  }
  ctx.PushMethodClass(defining);
  out = ExecInstanceMethodCall(method, self, expr, ctx, arena);
  ctx.PopMethodClass();
  return true;
}

const ClassTypeInfo* PackageQualifiedClassOf(const Expr* expr, SimContext& ctx,
                                             std::string_view& member) {
  if (expr == nullptr || expr->kind != ExprKind::kMemberAccess ||
      !expr->is_scope_resolution || expr->rhs == nullptr ||
      expr->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  const Expr* scope = expr->lhs;
  if (scope == nullptr || scope->kind != ExprKind::kMemberAccess ||
      !scope->is_scope_resolution || scope->lhs == nullptr ||
      scope->rhs == nullptr || scope->lhs->kind != ExprKind::kIdentifier ||
      scope->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  std::string key =
      std::string(scope->lhs->text) + "::" + std::string(scope->rhs->text);
  const ClassTypeInfo* cls = ctx.FindClassType(key);
  if (cls != nullptr) member = expr->rhs->text;
  return cls;
}

bool TryPackageClassStaticMember(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  std::string_view member;
  const ClassTypeInfo* cls = PackageQualifiedClassOf(expr, ctx, member);
  if (cls == nullptr) return false;
  auto it = cls->static_properties.find(std::string(member));
  if (it != cls->static_properties.end()) {
    out = it->second;
    return true;
  }
  // §8.26 with §26.7: an enum literal the class declares is reached the same
  // way, `std::process::RUNNING` naming the state §9.7 lists.
  auto eit = cls->enum_members.find(std::string(member));
  if (eit == cls->enum_members.end()) return false;
  out = MakeLogic4VecVal(arena, 32, eit->second);
  return true;
}

}  // namespace delta
