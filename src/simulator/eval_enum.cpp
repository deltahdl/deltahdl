#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

bool TryClassScopeEnumLiteral(std::string_view name, const ClassTypeInfo* cls,
                              Arena& arena, Logic4Vec& out) {
  for (; cls != nullptr; cls = cls->parent) {
    auto it = cls->enum_members.find(std::string(name));
    if (it == cls->enum_members.end()) continue;
    out = MakeLogic4VecVal(arena, 32, it->second);
    return true;
  }
  return false;
}

static Logic4Vec EnumFirst(const EnumTypeInfo& info, Arena& arena) {
  if (info.members.empty()) return MakeLogic4VecVal(arena, 32, 0);
  return MakeLogic4VecVal(arena, 32, info.members.front().value);
}

static Logic4Vec EnumLast(const EnumTypeInfo& info, Arena& arena) {
  if (info.members.empty()) return MakeLogic4VecVal(arena, 32, 0);
  return MakeLogic4VecVal(arena, 32, info.members.back().value);
}

static int FindMemberIndex(const EnumTypeInfo& info, uint64_t value) {
  for (size_t i = 0; i < info.members.size(); ++i) {
    if (info.members[i].value == value) return static_cast<int>(i);
  }
  return -1;
}

static Logic4Vec EnumNext(const EnumTypeInfo& info, uint64_t current,
                          uint32_t count, Arena& arena) {
  if (info.members.empty()) return MakeLogic4VecVal(arena, 32, 0);
  int idx = FindMemberIndex(info, current);
  if (idx < 0) return MakeLogic4VecVal(arena, 32, info.members.front().value);
  auto n = static_cast<int>(info.members.size());
  int new_idx = (idx + static_cast<int>(count % n)) % n;
  return MakeLogic4VecVal(arena, 32, info.members[new_idx].value);
}

static Logic4Vec EnumPrev(const EnumTypeInfo& info, uint64_t current,
                          uint32_t count, Arena& arena) {
  if (info.members.empty()) return MakeLogic4VecVal(arena, 32, 0);
  int idx = FindMemberIndex(info, current);
  if (idx < 0) return MakeLogic4VecVal(arena, 32, info.members.front().value);
  auto n = static_cast<int>(info.members.size());
  int offset = static_cast<int>(count % n);
  int new_idx = ((idx - offset) % n + n) % n;
  return MakeLogic4VecVal(arena, 32, info.members[new_idx].value);
}

static Logic4Vec EnumNum(const EnumTypeInfo& info, Arena& arena) {
  return MakeLogic4VecVal(arena, 32, info.members.size());
}

static Logic4Vec EnumName(const EnumTypeInfo& info, uint64_t current,
                          Arena& arena) {
  for (auto& m : info.members) {
    if (m.value != current) continue;
    auto name = m.name;
    uint32_t width = static_cast<uint32_t>(name.size()) * 8;
    if (width == 0) width = 8;
    auto vec = MakeLogic4Vec(arena, width);
    for (size_t i = 0; i < name.size(); ++i) {
      auto byte_idx = static_cast<uint32_t>(name.size() - 1 - i);
      uint32_t word = (byte_idx * 8) / 64;
      uint32_t bit = (byte_idx * 8) % 64;
      vec.words[word].aval |= static_cast<uint64_t>(name[i]) << bit;
    }
    return vec;
  }

  return MakeLogic4VecVal(arena, 8, 0);
}

static uint32_t ParseStepCount(const Expr* call_expr, SimContext& ctx,
                               Arena& arena) {
  if (call_expr->args.empty()) return 1;
  return static_cast<uint32_t>(
      EvalExpr(call_expr->args[0], ctx, arena).ToUint64());
}

struct EnumMethodArgs {
  const EnumTypeInfo& info;
  uint64_t current;
  const Expr* call_expr;
  SimContext& ctx;
  Arena& arena;
};

static bool DispatchEnumMethod(std::string_view method,
                               const EnumMethodArgs& args, Logic4Vec& out) {
  if (method == "first") {
    out = EnumFirst(args.info, args.arena);
    return true;
  }
  if (method == "last") {
    out = EnumLast(args.info, args.arena);
    return true;
  }
  if (method == "next") {
    uint32_t count = ParseStepCount(args.call_expr, args.ctx, args.arena);
    out = EnumNext(args.info, args.current, count, args.arena);
    return true;
  }
  if (method == "prev") {
    uint32_t count = ParseStepCount(args.call_expr, args.ctx, args.arena);
    out = EnumPrev(args.info, args.current, count, args.arena);
    return true;
  }
  if (method == "num") {
    out = EnumNum(args.info, args.arena);
    return true;
  }
  if (method == "name") {
    out = EnumName(args.info, args.current, args.arena);
    return true;
  }
  return false;
}

// §6.19.5 with §6.18: the enumeration a declared type names, resolved from
// where the declaration stands outward -- the scope the type wrote, `P::c_t`
// (§26.3); the declaring class, the classes enclosing it (§8.23) and the ones
// it extends, under the "C::name" keys the design's typedefs are registered
// by (RegisterDesignEnumTypes); the package the class is declared in; and the
// bare name a module declares or imports. Null for a type that names no
// registered enumeration.
struct DeclScope {
  const ClassTypeInfo* cls = nullptr;
  std::string_view package;
};

static const EnumTypeInfo* ScopedEnumType(std::string_view scope,
                                          std::string_view type_name,
                                          SimContext& ctx) {
  if (scope.empty()) return nullptr;
  return ctx.FindEnumType(std::string(scope) + "::" + std::string(type_name));
}

static const EnumTypeInfo* ClassScopedEnumType(const ClassTypeInfo* cls,
                                               std::string_view type_name,
                                               SimContext& ctx) {
  for (; cls != nullptr; cls = cls->enclosing) {
    for (const ClassTypeInfo* c = cls; c != nullptr; c = c->parent) {
      if (const auto* info = ScopedEnumType(c->name, type_name, ctx))
        return info;
    }
  }
  return nullptr;
}

static const EnumTypeInfo* EnumTypeOfDeclaredType(const DataType& type,
                                                  const DeclScope& scope,
                                                  SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed || type.type_name.empty())
    return nullptr;
  if (const auto* info = ScopedEnumType(type.scope_name, type.type_name, ctx))
    return info;
  if (const auto* info = ClassScopedEnumType(scope.cls, type.type_name, ctx))
    return info;
  std::string_view package =
      scope.cls != nullptr ? scope.cls->package : scope.package;
  if (const auto* info = ScopedEnumType(package, type.type_name, ctx))
    return info;
  return ctx.FindEnumType(type.type_name);
}

void RecordVariableEnumType(std::string_view var_name, const DataType& type,
                            SimContext& ctx) {
  const EnumTypeInfo* info =
      EnumTypeOfDeclaredType(type, {ctx.CurrentMethodClass(), {}}, ctx);
  if (info == nullptr) return;
  ctx.SetVariableEnumType(var_name, info->type_name);
}

// §6.19.5.1 through §6.19.5.4 give first(), last(), next() and prev() the
// enumeration's own type as their result, so a call written as `e.m()` with
// `e` one of those calls is itself an enum method call on that type.
static bool ReturnsTheEnumType(std::string_view method) {
  return method == "first" || method == "last" || method == "next" ||
         method == "prev";
}

// §8.7 with §6.20: the declared type of the property, static property or
// parameter `name` of `cls` or of a class it extends, and the class declaring
// it, or null where none declares it. The declaration is asked because the
// value held is not: a stored member is a packed value (§5.9) carrying no
// type.
static const DataType* ClassMemberDeclaredType(const ClassTypeInfo* cls,
                                               std::string_view name,
                                               const ClassTypeInfo*& declarer) {
  for (const ClassTypeInfo* c = cls; c != nullptr; c = c->parent) {
    if (c->decl == nullptr) continue;
    for (const ClassMember* m : c->decl->members) {
      if (m->kind != ClassMemberKind::kProperty || m->name != name) continue;
      // §7.4 and §7.8: a member declared with unpacked dimensions is an array
      // of the enumeration, not a value of it, and `aa.first(i)` on it is
      // the array's method (§7.8.4).
      if (!m->unpacked_dims.empty()) return nullptr;
      declarer = c;
      return &m->data_type;
    }
  }
  return nullptr;
}

static const EnumTypeInfo* EnumTypeOfClassMember(const ClassTypeInfo* cls,
                                                 std::string_view name,
                                                 SimContext& ctx) {
  const ClassTypeInfo* declarer = nullptr;
  const DataType* type = ClassMemberDeclaredType(cls, name, declarer);
  if (type == nullptr) return nullptr;
  return EnumTypeOfDeclaredType(*type, {declarer, {}}, ctx);
}

// §8.10 and §8.11: the class scope a bare name inside a method resolves
// against -- the class whose static property it names, the running method's
// class, or the object's own -- as EvalIdentifierClassScope (evaluation.cpp)
// resolves it; null outside every method.
static const ClassTypeInfo* BareNameClassScope(std::string_view name,
                                               SimContext& ctx) {
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  if (method_cls != nullptr) {
    const ClassTypeInfo* owner = method_cls->StaticPropertyOwner(name);
    return owner != nullptr ? owner : method_cls;
  }
  const ClassObject* self = ctx.CurrentThis();
  return self != nullptr ? self->type : nullptr;
}

// §6.19: the enumeration declaring the member literal `name`: one of the
// class scope's, walking the classes enclosing it (§8.23), else one visible
// where the literal is written.
static const EnumTypeInfo* EnumTypeOfLiteral(std::string_view name,
                                             const ClassTypeInfo* cls,
                                             SimContext& ctx) {
  for (; cls != nullptr; cls = cls->enclosing) {
    if (const auto* info = ctx.FindEnumTypeDeclaringMember(name, cls->name))
      return info;
  }
  return ctx.FindEnumTypeDeclaringMember(name, {});
}

// Whether `e` is a name or a chain of member selects down from one, `h` or
// `d.c`: reading it runs no subroutine, so it can be evaluated to find the
// object it denotes and evaluated again for the value the method starts from.
static bool IsNamePath(const Expr* e) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) return true;
  return e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution &&
         e->rhs != nullptr && e->rhs->kind == ExprKind::kIdentifier &&
         IsNamePath(e->lhs);
}

// §8.3, §8.11 and §8.15: the class whose declarations a member select through
// `base` reads -- the object's own for a handle or a chain of them and for
// `this`, and the parent of the running method's class for `super` -- or
// null where `base` denotes no object.
static const ClassTypeInfo* ClassBehindHandle(const Expr* base, SimContext& ctx,
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

// A bare name: the variable it denotes, when its declaration wrote an
// enumeration (§23.9 has a variable of the name stand ahead of a class
// scope's member), or the member literal the variable is, a module's or a
// package's literal standing as a variable of the scope under its name
// (BuildEnumMembers in src/elaborator/elaborator_typedef.cpp); else the
// property, static property or parameter of the class scope a name inside a
// method resolves against (§8.10, §8.11); else the literal of a class-scoped
// enumeration (§8.23).
static const EnumTypeInfo* EnumTypeOfName(const Expr* e, SimContext& ctx) {
  if (e->text == "this" || e->text == "super") return nullptr;
  std::string key = IdentifierLookupKey(e);
  if (NameDenotesVariable(key, ctx)) {
    if (const auto* info = ctx.GetVariableEnumType(key)) return info;
    return EnumTypeOfLiteral(e->text, nullptr, ctx);
  }
  const ClassTypeInfo* cls = BareNameClassScope(e->text, ctx);
  if (const auto* info = EnumTypeOfClassMember(cls, e->text, ctx)) return info;
  return EnumTypeOfLiteral(e->text, cls, ctx);
}

// `C::se`, `C::LC`, `C::RED` (§8.9, §8.23, §8.25 through a specialization's
// `C#(X)::LC`) and `P::pc`, `P::EC`, `P::RED` (§26.3): a class's member or
// literal, or a package's variable, parameter or literal under the "P.name"
// key the package's storage stands under.
static const EnumTypeInfo* EnumTypeOfScopedName(std::string_view scope,
                                                std::string_view member,
                                                SimContext& ctx) {
  if (const ClassTypeInfo* cls = ctx.FindClassType(scope)) {
    if (const auto* info = EnumTypeOfClassMember(cls, member, ctx)) return info;
    return EnumTypeOfLiteral(member, cls, ctx);
  }
  std::string key = std::string(scope) + "." + std::string(member);
  if (const auto* info = ctx.GetVariableEnumType(key)) return info;
  return ctx.FindEnumTypeDeclaringMember(member, scope);
}

// §13.4 with §8.7: the declared result type of the method `name` of `cls` or
// of a class it extends, resolved in the declaring class.
static const EnumTypeInfo* EnumTypeOfMethodResult(const ClassTypeInfo* cls,
                                                  std::string_view name,
                                                  SimContext& ctx) {
  for (const ClassTypeInfo* c = cls; c != nullptr; c = c->parent) {
    auto it = c->methods.find(std::string(name));
    if (it == c->methods.end()) continue;
    return EnumTypeOfDeclaredType(it->second->return_type, {c, {}}, ctx);
  }
  return nullptr;
}

// §13.4: the declared result type of a bare callee -- a function of the
// module, of a package the module imports or the running frame's package
// (§26.3), or a method of the running method's class named bare (§8.6).
static const EnumTypeInfo* EnumTypeOfBareCallResult(std::string_view name,
                                                    SimContext& ctx) {
  ModuleItem* func = ctx.FindFunction(name);
  if (func == nullptr) func = ctx.FindFunctionInPackageScope(name);
  if (func != nullptr)
    return EnumTypeOfDeclaredType(func->return_type, {}, ctx);
  const ClassObject* self = ctx.CurrentThis();
  if (self == nullptr) return nullptr;
  const ClassTypeInfo* running = ctx.CurrentMethodClass();
  return EnumTypeOfMethodResult(running != nullptr ? running : self->type, name,
                                ctx);
}

// §8.9 and §26.3: the declared result type of `C::m()`, a static method of
// the class, or of `P::f()`, a package's function under the "P::f" key
// RegisterPackageScopedSubroutines enters it by.
static const EnumTypeInfo* EnumTypeOfScopedCallResult(std::string_view scope,
                                                      std::string_view name,
                                                      SimContext& ctx) {
  if (const ClassTypeInfo* cls = ctx.FindClassType(scope))
    return EnumTypeOfMethodResult(cls, name, ctx);
  ModuleItem* func =
      ctx.FindFunction(std::string(scope) + "::" + std::string(name));
  if (func == nullptr) return nullptr;
  return EnumTypeOfDeclaredType(func->return_type, {nullptr, scope}, ctx);
}

// §13.4 with §8.9 and §26.3: the declared result type of the subroutine a
// call names -- a bare function or method, a static method or package
// function through a scope, or a method through a handle, `this` or `super`.
static const EnumTypeInfo* EnumTypeOfSubroutineResult(const Expr* callee,
                                                      SimContext& ctx,
                                                      Arena& arena) {
  if (callee->kind == ExprKind::kIdentifier)
    return EnumTypeOfBareCallResult(callee->text, ctx);
  if (callee->kind != ExprKind::kMemberAccess || callee->lhs == nullptr ||
      callee->rhs == nullptr || callee->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  if (!callee->is_scope_resolution) {
    return EnumTypeOfMethodResult(ClassBehindHandle(callee->lhs, ctx, arena),
                                  callee->rhs->text, ctx);
  }
  if (callee->lhs->kind != ExprKind::kIdentifier) return nullptr;
  return EnumTypeOfScopedCallResult(callee->lhs->text, callee->rhs->text, ctx);
}

// A member select: `C::x` or `P::x` through a scope, else a member of the
// class behind a handle, a chain of them, `this` or `super`.
static const EnumTypeInfo* EnumTypeOfMemberAccess(const Expr* e,
                                                  SimContext& ctx,
                                                  Arena& arena) {
  if (e->lhs == nullptr || e->rhs == nullptr ||
      e->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  if (!e->is_scope_resolution) {
    // §6.19.5.7: `c.next` with no argument list is the call, and one of the
    // enumeration's own type (§6.19.5.3), so `c.next.name` chains as
    // `c.next().name()` does.
    if (ReturnsTheEnumType(e->rhs->text)) {
      if (const auto* info = EnumTypeOfExpr(e->lhs, ctx, arena)) return info;
    }
    return EnumTypeOfClassMember(ClassBehindHandle(e->lhs, ctx, arena),
                                 e->rhs->text, ctx);
  }
  if (e->lhs->kind != ExprKind::kIdentifier) return nullptr;
  return EnumTypeOfScopedName(e->lhs->text, e->rhs->text, ctx);
}

// Whether the call `e` is one of the §6.19.5 methods that answer the
// enumeration's own type, `x.next()`, whose result is of its receiver's type.
static bool IsEnumTypedMethodCall(const Expr* e) {
  const Expr* callee = e->lhs;
  return callee != nullptr && callee->kind == ExprKind::kMemberAccess &&
         !callee->is_scope_resolution && callee->rhs != nullptr &&
         callee->rhs->kind == ExprKind::kIdentifier &&
         ReturnsTheEnumType(callee->rhs->text);
}

// §6.24.1 with A.8.4: a static cast is a primary of its casting type, so
// `Cols'(2)` is an expression of the enumeration Cols and `C::e_t'(1)` of
// the class-scoped one (§8.23). The casting type stands in the cast's rhs as
// the parser read it, a name or a scoped name, and a cast written with a
// keyword type (`int'(x)`, held in the node's text) names no enumeration.
static const EnumTypeInfo* EnumTypeOfCast(const Expr* e, SimContext& ctx) {
  const Expr* type_node = e->rhs;
  if (type_node == nullptr) return nullptr;
  DataType type;
  type.kind = DataTypeKind::kNamed;
  if (type_node->kind == ExprKind::kIdentifier) {
    type.scope_name = type_node->scope_prefix;
    type.type_name = type_node->text;
  } else if (type_node->kind == ExprKind::kMemberAccess &&
             type_node->is_scope_resolution && type_node->lhs != nullptr &&
             type_node->rhs != nullptr &&
             type_node->lhs->kind == ExprKind::kIdentifier &&
             type_node->rhs->kind == ExprKind::kIdentifier) {
    type.scope_name = type_node->lhs->text;
    type.type_name = type_node->rhs->text;
  } else {
    return nullptr;
  }
  return EnumTypeOfDeclaredType(type, {ctx.CurrentMethodClass(), {}}, ctx);
}

// The enumeration an expression carries, by the declaration behind it, as
// deep as a chain of calls is written (`s.first().next().name()`); described
// in evaluation.h.
const EnumTypeInfo* EnumTypeOfExpr(const Expr* e, SimContext& ctx,
                                   Arena& arena) {
  if (e == nullptr) return nullptr;
  if (e->kind == ExprKind::kIdentifier) return EnumTypeOfName(e, ctx);
  if (e->kind == ExprKind::kCast) return EnumTypeOfCast(e, ctx);
  if (e->kind == ExprKind::kMemberAccess)
    return EnumTypeOfMemberAccess(e, ctx, arena);
  if (e->kind != ExprKind::kCall || e->lhs == nullptr) return nullptr;
  if (IsEnumTypedMethodCall(e)) {
    if (const auto* info = EnumTypeOfExpr(e->lhs->lhs, ctx, arena)) return info;
  }
  return EnumTypeOfSubroutineResult(e->lhs, ctx, arena);
}

// The value the method starts from: the variable's own for a name denoting
// one, and for any other receiver the value it evaluates to -- a property, a
// literal, a call's result, evaluated through this same dispatch when it is a
// chained method.
static uint64_t CurrentValueOfBase(const Expr* base, SimContext& ctx,
                                   Arena& arena) {
  if (base->kind == ExprKind::kIdentifier) {
    std::string key = IdentifierLookupKey(base);
    if (NameDenotesVariable(key, ctx))
      return ctx.FindVariable(key)->value.ToUint64();
  }
  return EvalExpr(base, ctx, arena).ToUint64();
}

// The six method names of §6.19.5.1 through §6.19.5.6, asked before the
// receiver is resolved, since resolving a receiver that is a handle path
// reads the handle, which every other member select or method call has no
// reason to do here.
static bool IsEnumMethodName(std::string_view method) {
  return ReturnsTheEnumType(method) || method == "num" || method == "name";
}

// The method the member select `access` names, on the enumeration its
// receiver carries, with the arguments of `call_expr` -- the call's, or none
// where the select stands alone (§6.19.5.7).
static bool TryEvalEnumMethod(const Expr* access, const Expr* call_expr,
                              SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution || access->lhs == nullptr ||
      access->rhs == nullptr || access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (!IsEnumMethodName(access->rhs->text)) return false;
  const auto* info = EnumTypeOfExpr(access->lhs, ctx, arena);
  if (!info) return false;
  uint64_t current = CurrentValueOfBase(access->lhs, ctx, arena);
  EnumMethodArgs args{*info, current, call_expr, ctx, arena};
  return DispatchEnumMethod(access->rhs->text, args, out);
}

bool TryEvalEnumMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  return TryEvalEnumMethod(expr->lhs, expr, ctx, arena, out);
}

bool TryEvalEnumMethodWithoutArgs(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  return TryEvalEnumMethod(expr, expr, ctx, arena, out);
}

}  // namespace delta
