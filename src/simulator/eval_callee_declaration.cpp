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

// What a callee naming no declared subroutine answers: an implicit result
// type, which names no type a result could be read as.
CalleeDeclaration Undeclared() {
  static const DataType kNoResult{};
  return {&kNoResult, nullptr, {}};
}

// Whether `e` is a name or a chain of member selects down from one, `h` or
// `d.c`: reading it runs no subroutine, so it can be evaluated to find the
// object it denotes and evaluated again for the value the method starts from.
bool IsNamePath(const Expr* e) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) return true;
  return e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution &&
         e->rhs != nullptr && e->rhs->kind == ExprKind::kIdentifier &&
         IsNamePath(e->lhs);
}

// §13.4 with §8.7: the method `name` of `cls` or of a class it extends, its
// result resolved in the declaring class.
CalleeDeclaration MethodDeclaration(const ClassTypeInfo* cls,
                                    std::string_view name) {
  for (const ClassTypeInfo* c = cls; c != nullptr; c = c->parent) {
    auto it = c->methods.find(std::string(name));
    if (it == c->methods.end()) continue;
    return {&it->second->return_type, c, {}};
  }
  return Undeclared();
}

// §13.4: a bare callee -- a function of the module, of a package the module
// imports or the running frame's package (§26.3), or a method of the running
// method's class named bare (§8.6).
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

// §8.9 and §26.3: `C::m()`, a static method of the class, or `P::f()`, a
// package's function under the "P::f" key RegisterPackageScopedSubroutines
// enters it by.
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
