#include "simulator/eval_callee_declaration.h"

#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

CalleeDeclaration Undeclared() {
  static const DataType kNoResult{};
  return {&kNoResult, nullptr, {}};
}

bool IsNamePath(const Expr* e) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) return true;
  return e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution &&
         e->rhs != nullptr && e->rhs->kind == ExprKind::kIdentifier &&
         IsNamePath(e->lhs);
}

CalleeDeclaration MethodDeclaration(const ClassTypeInfo* cls,
                                    std::string_view name) {
  for (const ClassTypeInfo* c = cls; c != nullptr; c = c->parent) {
    auto it = c->methods.find(std::string(name));
    if (it == c->methods.end()) continue;
    return {&it->second->return_type, c, {}};
  }
  return Undeclared();
}

CalleeDeclaration BareCalleeDeclaration(std::string_view name,
                                        SimContext& ctx) {
  ModuleItem* func = ctx.FindFunction(name);
  if (func == nullptr) func = ctx.FindFunctionInPackageScope(name);
  if (func != nullptr) return {&func->return_type, nullptr, {}};
  const ClassObject* self = ctx.CurrentThis();
  if (self == nullptr) return Undeclared();
  const ClassTypeInfo* running = ctx.CurrentMethodClass();
  return MethodDeclaration(running != nullptr ? running : self->type, name);
}

CalleeDeclaration ScopedCalleeDeclaration(std::string_view scope,
                                          std::string_view name,
                                          SimContext& ctx) {
  if (const ClassTypeInfo* cls = ctx.FindClassType(scope))
    return MethodDeclaration(cls, name);
  ModuleItem* func =
      ctx.FindFunction(std::string(scope) + "::" + std::string(name));
  if (func == nullptr) return Undeclared();
  return {&func->return_type, nullptr, scope};
}

}  // namespace

const ClassTypeInfo* ClassBehindHandle(const Expr* base, SimContext& ctx,
                                       Arena& arena) {
  if (base->kind == ExprKind::kIdentifier && base->text == "super") {
    const ClassTypeInfo* running = ctx.CurrentMethodClass();
    if (running != nullptr) return running->parent;
    const ClassObject* self = ctx.CurrentThis();
    return self != nullptr && self->type != nullptr ? self->type->parent
                                                    : nullptr;
  }
  if (base->kind == ExprKind::kIdentifier && base->text == "this") {
    const ClassObject* self = ctx.CurrentThis();
    return self != nullptr ? self->type : nullptr;
  }
  if (!IsNamePath(base)) return nullptr;
  const ClassObject* obj =
      ctx.GetClassObject(EvalExpr(base, ctx, arena).ToUint64());
  return obj != nullptr ? obj->type : nullptr;
}

CalleeDeclaration DeclarationOfCallee(const Expr* callee, SimContext& ctx,
                                      Arena& arena) {
  if (callee->kind == ExprKind::kIdentifier)
    return BareCalleeDeclaration(callee->text, ctx);
  if (callee->kind != ExprKind::kMemberAccess || callee->lhs == nullptr ||
      callee->rhs == nullptr || callee->rhs->kind != ExprKind::kIdentifier) {
    return Undeclared();
  }
  if (!callee->is_scope_resolution) {
    return MethodDeclaration(ClassBehindHandle(callee->lhs, ctx, arena),
                             callee->rhs->text);
  }
  if (callee->lhs->kind != ExprKind::kIdentifier) return Undeclared();
  return ScopedCalleeDeclaration(callee->lhs->text, callee->rhs->text, ctx);
}

}  // namespace delta
