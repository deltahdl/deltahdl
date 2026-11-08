#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/eval_class_params.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

void RunStaticMethodInClassScope(ClassMethodTarget target, const Expr* expr,
                                 SimContext& ctx, Arena& arena,
                                 Logic4Vec& out) {
  auto params = CollectClassParamBindings(target.param_cls, ctx);
  ctx.PushScope();
  RebindClassParamBindings(params, ctx);
  ctx.PushMethodClass(target.param_cls);
  ExecClassMethod(target, expr, ctx, arena, out);
  WritebackOutputArgs(target.method, expr, ctx, arena);
  ctx.PopMethodClass();
  ctx.PopScope();
}

bool TryEvalEnclosingStaticCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  const ClassTypeInfo* cls = ctx.CurrentMethodClass();
  if (!cls) return false;
  std::string name(expr->callee);
  for (const ClassTypeInfo* t = cls; t != nullptr; t = t->parent) {
    auto it = t->methods.find(name);
    if (it == t->methods.end()) continue;
    if (!it->second->is_static_method) return false;
    RunStaticMethodInClassScope({it->second, t}, expr, ctx, arena, out);
    return true;
  }
  return false;
}

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
  if (const ClassTypeInfo* declarer = cls->StaticPropertyDeclarer(member)) {
    out = declarer->static_properties.find(std::string(member))->second;
    return true;
  }
  auto eit = cls->enum_members.find(std::string(member));
  if (eit == cls->enum_members.end()) return false;
  out = ClassEnumLiteral(*cls, eit->first, eit->second, arena);
  return true;
}

}  // namespace delta
