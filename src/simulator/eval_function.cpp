#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

// Stores `val` as the initial value of `prop` on `obj`: §7.4.2 has a
// property declared as an array hold its elements one by one, each
// initialized as the one value would be, and §7.5 one declared with a
// dynamic dimension hold no element until `new[]` sizes it; any other
// property is stored under its bare and its class-scoped name.
static void StoreClassPropertyDefault(const ClassTypeInfo* info,
                                      const ClassTypeInfo::PropertyInfo& prop,
                                      const Logic4Vec& val, ClassObject* obj,
                                      Arena& arena) {
  if (prop.is_dynamic) {
    obj->properties[ClassArraySizeKey(prop.name)] =
        MakeLogic4VecVal(arena, 32, 0);
    return;
  }
  if (prop.array_size > 0) {
    for (uint32_t i = 0; i < prop.array_size; ++i) {
      obj->properties[ClassArrayElementKey(prop.name, prop.array_lo + i)] =
          OwnRhsWords(val, arena);
    }
    return;
  }
  obj->properties[std::string(prop.name)] = val;
  std::string scoped = std::string(info->name) + "::" + std::string(prop.name);
  obj->properties[scoped] = val;
}

static void InitClassPropertyDefaults(const ClassTypeInfo* info,
                                      ClassObject* obj, SimContext& ctx,
                                      Arena& arena) {
  for (const auto& prop : info->properties) {
    // §8.9: a static property is one shared copy that lives on the class type,
    // created and initialized once. Constructing an object must not give it a
    // private per-instance copy, or instance-qualified access would shadow the
    // shared storage. Leave static properties out of the instance map so reads
    // and writes fall through to the type's shared static_properties.
    if (prop.is_static) continue;
    // §8.7: a property is initialized to its explicit default if one is given,
    // otherwise to its type's uninitialized value — X for a 4-state type, 0 for
    // a 2-state one — rather than being forced to zero.
    Logic4Vec val;
    if (prop.init_expr) {
      // §6.8 executes a declaration's initializer as an assignment to the
      // declared object, so it is coerced into the property exactly as a later
      // write to it is. The two arms below already size from prop.width, which
      // is what made this one's silence visible.
      val = CoerceToPropertyType(info, prop.name,
                                 EvalExpr(prop.init_expr, ctx, arena), arena);
    } else if (prop.is_4state) {
      val = MakeAllX(arena, prop.width);
    } else {
      val = MakeLogic4VecVal(arena, prop.width, 0);
    }
    StoreClassPropertyDefault(info, prop, val, obj, arena);
  }

  if (info->decl) {
    for (const auto& [pname, pexpr] : info->decl->params) {
      if (pexpr) {
        // §6.8 makes the object's stored parameter and whatever the default
        // expression read two data storage elements, each storing "a value
        // from one assignment to the next". EvalExpr on a bare identifier
        // answers with the variable's own vector (evaluation.cpp), and a
        // Logic4Vec copy carries the words pointer rather than the words
        // (src/common/types.h), so storing it as it arrived left the two as
        // one buffer. The property arm above reaches the same copy through
        // CoerceToPropertyType; this arm coerces nothing, so it takes it here.
        // The bare and the scoped key are two names for the one parameter and
        // every writer sets both, so they share the one copy as they do above.
        auto val = OwnRhsWords(EvalExpr(pexpr, ctx, arena), arena);
        obj->properties[std::string(pname)] = val;
        std::string scoped =
            std::string(info->name) + "::" + std::string(pname);
        obj->properties[scoped] = val;
      }
    }
  }
}

// §8.7: the actuals of a `new(...)` call are the caller's expressions, so they
// are bound with the caller's `this` and class in force, the object under
// construction taken off the stack for the binding and put back after:
// `next = new(depth - 1)` in a method of the class reads the method's own
// object, where with the fresh object on top it read that object's `depth`,
// still at its default, and constructed a chain that never ended.
static void BindCallerConstructorArgs(const ModuleItem* ctor,
                                      const Expr* args_expr, SimContext& ctx,
                                      Arena& arena) {
  ClassObject* constructed = ctx.CurrentThis();
  ctx.PopThis();
  BindFunctionArgs(ctor, args_expr, ctx, arena);
  ctx.PushThis(constructed);
}

// Runs one level's constructor. `args_are_callers` says the actuals are the
// `new` call's own, the caller's expressions; otherwise they are the
// extends-specifier or forwarded arguments the level below synthesized, which
// are expressions of the derived class and read the object under
// construction.
static void RunConstructorForLevel(const ClassTypeInfo* info,
                                   const Expr* args_expr, bool args_are_callers,
                                   SimContext& ctx, Arena& arena) {
  auto it = info->methods.find("new");
  if (it == info->methods.end() || !it->second) return;
  ctx.PushScope();
  if (args_expr && args_are_callers) {
    BindCallerConstructorArgs(it->second, args_expr, ctx, arena);
  }
  // §8.15/§8.17: while this constructor body runs, `super` resolves relative to
  // `info` (the lexically enclosing class), not the dynamic type of the object.
  ctx.PushMethodClass(info);
  if (args_expr && !args_are_callers) {
    BindFunctionArgs(it->second, args_expr, ctx, arena);
  }
  Variable dummy;
  ExecFunctionBody(it->second, &dummy, ctx, arena);
  ctx.PopMethodClass();
  ctx.PopScope();
}

static size_t FindFirstDefaultArgPos(const ModuleItem* method) {
  for (size_t j = 0; j < method->func_args.size(); ++j) {
    if (method->func_args[j].is_default) {
      return j;
    }
  }
  return 0;
}

static size_t FindChildNewDefaultPos(const ClassDecl* child_decl) {
  for (const auto* m : child_decl->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      return FindFirstDefaultArgPos(m->method);
    }
  }
  return 0;
}

static const Expr* SynthDefaultExtendsArgs(const ClassTypeInfo* base,
                                           const ClassDecl* child_decl,
                                           const Expr* new_expr, Arena& arena) {
  size_t default_pos = FindChildNewDefaultPos(child_decl);

  size_t base_argc = 0;
  auto base_it = base->methods.find("new");
  if (base_it != base->methods.end() && base_it->second) {
    base_argc = base_it->second->func_args.size();
  }
  auto* synth = arena.Create<Expr>();
  synth->kind = ExprKind::kCall;
  for (size_t j = 0; j < base_argc && default_pos + j < new_expr->args.size();
       ++j) {
    synth->args.push_back(new_expr->args[default_pos + j]);
  }
  return synth;
}

// §8.17: whether the child class's own 'new' constructor argument list uses the
// 'default' keyword. When it does, the trailing actuals of the derived-most
// new() call expand to the superclass constructor's argument list.
static bool ChildNewUsesDefaultArg(const ClassDecl* child_decl) {
  for (const auto* m : child_decl->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      for (const auto& a : m->method->func_args) {
        if (a.is_default) return true;
      }
      return false;
    }
  }
  return false;
}

static const Expr* ResolveConstructorArgsForLevel(
    const std::vector<const ClassTypeInfo*>& chain, size_t i,
    const Expr* new_expr, Arena& arena) {
  const Expr* args = (i == chain.size() - 1) ? new_expr : nullptr;
  if (args || i + 1 >= chain.size() || !chain[i + 1]->decl) return args;

  const auto* child_decl = chain[i + 1]->decl;
  if (!child_decl->extends_args.empty()) {
    auto* synth = arena.Create<Expr>();
    synth->kind = ExprKind::kCall;
    synth->args = child_decl->extends_args;
    return synth;
  }
  // §8.17: 'default' expands to the superclass constructor arguments, whether
  // it appears in the extends specifier (Base(default)) or in the subclass
  // constructor's own argument list (new(..., default)). Either way the
  // trailing actuals of the new() call are forwarded to this base level. This
  // also realizes the compiler-inserted super.new(default) when the subclass
  // body provides no explicit call.
  if ((child_decl->extends_has_default || ChildNewUsesDefaultArg(child_decl)) &&
      new_expr) {
    return SynthDefaultExtendsArgs(chain[i], child_decl, new_expr, arena);
  }
  return args;
}

Logic4Vec EvalClassNew(std::string_view class_type, const Expr* new_expr,
                       SimContext& ctx, Arena& arena, SourceLoc loc) {
  auto* info = ctx.FindClassType(class_type);
  if (!info) return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  if (info->is_abstract) {
    ctx.GetDiag().Error(loc,
                        "cannot construct object of abstract class '" +
                            std::string(class_type) + "'",
                        Subclause("8.21"));
    return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  }
  if (info->is_interface) {
    ctx.GetDiag().Error(loc,
                        "cannot construct object of interface class '" +
                            std::string(class_type) + "'",
                        Subclause("8.26.5"));
    return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  }
  auto* obj = arena.Create<ClassObject>();
  obj->type = info;

  std::vector<const ClassTypeInfo*> chain;
  for (const auto* cur = info; cur; cur = cur->parent) chain.push_back(cur);
  std::reverse(chain.begin(), chain.end());

  auto handle = ctx.AllocateClassObject(obj);
  ctx.PushThis(obj);

  for (size_t i = 0; i < chain.size(); ++i) {
    // §8.7: a property's default expression belongs to the class declaring it,
    // so unqualified names resolve as they do in that class's methods -- the
    // reason the constructor body below runs under the same enclosing class.
    // Without it the read takes the object's most-derived view of the name,
    // which only a write from the most-derived class refreshes, so a base
    // constructor's assignment is left behind and a derived property
    // initialized from a base one sees the base's declared default instead.
    ctx.PushMethodClass(chain[i]);
    InitClassPropertyDefaults(chain[i], obj, ctx, arena);
    ctx.PopMethodClass();
    const Expr* args =
        ResolveConstructorArgsForLevel(chain, i, new_expr, arena);
    RunConstructorForLevel(chain[i], args, args == new_expr, ctx, arena);
  }

  ctx.PopThis();
  return MakeLogic4VecVal(arena, 64, handle);
}

void ApplyClassParamOverrides(std::string_view var_name, uint64_t handle,
                              SimContext& ctx, Arena& arena) {
  auto* obj = ctx.GetClassObject(handle);
  if (!obj || !obj->type || !obj->type->decl) return;
  const auto& param_exprs = ctx.GetVariableClassParamExprs(var_name);
  if (param_exprs.empty()) return;
  const auto& params = obj->type->decl->params;
  for (size_t i = 0; i < params.size() && i < param_exprs.size(); ++i) {
    if (param_exprs[i]) {
      // §6.8, as in the default arm of InitClassPropertyDefaults above: the
      // object's stored parameter and whatever the override expression read
      // are two data storage elements, and a Logic4Vec copy carries the words
      // pointer rather than the words, so `C #(.W(n)) c;` stored as it arrived
      // left the object and the variable n as one buffer. One copy serves both
      // keys, which are two names for the one parameter.
      auto val = OwnRhsWords(EvalExpr(param_exprs[i], ctx, arena), arena);
      obj->properties[std::string(params[i].first)] = val;
      std::string scoped =
          std::string(obj->type->name) + "::" + std::string(params[i].first);
      obj->properties[scoped] = val;
    }
  }
}

// ClassMethodTarget and the ExecClassMethod prototype live in
// eval_function_internal.h (so eval_static_method.cpp can run a method body
// without a `this`); the definition is below.

bool ResolveInstanceMethod(const MethodCallParts& parts, SimContext& ctx,
                           InstanceMethodInfo& info) {
  auto class_type = ctx.GetVariableClassType(parts.var_name);
  if (class_type.empty()) return false;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return false;
  auto handle = var->value.ToUint64();
  if (handle == kNullClassHandle) return false;
  info.obj = ctx.GetClassObject(handle);
  if (!info.obj) return false;
  info.method = info.obj->ResolveVirtualMethod(parts.method_name, &info.owner);
  if (!info.method) {
    auto* declared_type = ctx.FindClassType(class_type);
    // §8.26.9: a non-interface declared type resolves against that type; an
    // interface-class declared type (or no declared type at all) resolves via
    // the object's dynamic type (the implementing class).
    const ClassTypeInfo* from = (declared_type && !declared_type->is_interface)
                                    ? declared_type
                                    : info.obj->type;
    info.method =
        info.obj->ResolveMethodForType(parts.method_name, from, &info.owner);
  }
  return info.method != nullptr;
}

Logic4Vec ExecInstanceMethodCall(ModuleItem* method, ClassObject* obj,
                                 const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  Logic4Vec out;
  ctx.PushScope();
  ctx.PushThis(obj);
  ctx.PushQueueRefFrame();
  ctx.PushAssocRefFrame();
  ExecClassMethod({method}, expr, ctx, arena, out);
  // §13.5.2: the actual an output argument is copied back to is an expression
  // of the caller's, so the copy-out is made with the caller's `this` in
  // scope: a method passing its own property, `other.get(vif)`, names a
  // property of its own object, and with the callee's object still pushed the
  // value landed on that object instead.
  ctx.PopThis();
  WritebackOutputArgs(method, expr, ctx, arena);
  WritebackQueueRefs(ctx);
  WritebackAssocRefs(ctx);
  ctx.PopScope();
  return out;
}

static bool TryEvalSuperMethodCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (parts.var_name != "super") return false;
  // §8.17: super.new(default) forwards the constructor's default-expanded
  // arguments to the superclass. The flattened constructor chain already ran
  // the superclass constructor once with those forwarded actuals (see
  // ResolveConstructorArgsForLevel), so the explicit call here is satisfied
  // without a second base-constructor invocation -- which would otherwise bind
  // the literal 'default' token as an ordinary argument value.
  if (parts.method_name == "new" && expr->args.size() == 1 && expr->args[0] &&
      expr->args[0]->kind == ExprKind::kIdentifier &&
      expr->args[0]->text == "default") {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  auto* self = ctx.CurrentThis();
  if (!self || !self->type) return false;
  // §8.15: `super` refers to the parent of the lexically enclosing class. Using
  // the dynamic type of `this` here made super.new() in a mid-hierarchy
  // constructor resolve back to the same level and recurse forever.
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  const ClassTypeInfo* super_type =
      enclosing ? enclosing->parent : self->type->parent;
  if (!super_type) return false;
  const ClassTypeInfo* defining = nullptr;
  auto* method =
      self->ResolveMethodForType(parts.method_name, super_type, &defining);
  if (!method) return false;
  // Run the resolved method with its own defining class as the enclosing scope
  // so a nested super call walks one level further up, not back to here.
  ctx.PushMethodClass(defining);
  out = ExecInstanceMethodCall(method, self, expr, ctx, arena);
  ctx.PopMethodClass();
  return true;
}

static bool TryEvalClassMethodCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  InstanceMethodInfo info;
  if (!ResolveInstanceMethod(parts, ctx, info)) return false;
  // §8.10/§8.9: a static method invoked through an instance handle shares the
  // class's single static storage; dispatch it in class scope (no `this`).
  if (info.method->is_static) {
    RunStaticMethodInClassScope({info.method, info.obj->type}, expr, ctx, arena,
                                out);
    return true;
  }
  // Run the body with its defining class as the enclosing scope so an
  // unqualified member resolves to that level even when a derived class
  // shadows the name (§8.15).
  ctx.PushMethodClass(info.owner);
  out = ExecInstanceMethodCall(info.method, info.obj, expr, ctx, arena);
  ctx.PopMethodClass();
  return true;
}

void BindClassParams(const ClassTypeInfo* cls, const Expr* base_id,
                     SimContext& ctx, Arena& arena) {
  if (!cls->decl) return;
  const auto& params = cls->decl->params;
  const auto& values = base_id->elements;
  for (size_t i = 0; i < params.size(); ++i) {
    Logic4Vec val;
    if (i < values.size()) {
      val = EvalExpr(values[i], ctx, arena);
    } else if (params[i].second) {
      val = EvalExpr(params[i].second, ctx, arena);
    } else {
      val = MakeLogic4VecVal(arena, 32, 0);
    }
    auto* v = ctx.CreateLocalVariable(params[i].first, val.width);
    v->value = val;
    // §8.25.1: the same parameter is reachable inside the class -- and inside
    // its out-of-block methods, which resolve as though written in the class --
    // through the class scope resolution operator (`C::p`), which the evaluator
    // sees as a "Class.param" member reference. Bind that compound name to the
    // same value so `C::p` tracks the active specialization exactly as the bare
    // name `p` does, and is never shadowed by a same-named local variable.
    auto* qname = arena.Create<std::string>(std::string(cls->decl->name) + "." +
                                            std::string(params[i].first));
    auto* qv = ctx.CreateLocalVariable(*qname, val.width);
    qv->value = val;
  }
}

struct ClassScopeInfo {
  const Expr* access;
  // The class as the call named it: a bare `C` or, through the package scope
  // resolution operator of §26.3, `p::C`, the key the lowerer binds a package's
  // class under whether or not the package was imported.
  std::string_view class_name;
  ClassTypeInfo* cls;
  ModuleItem* method;
  bool is_void;
};

// §8.23 has the left operand of `::` name a class or a package, and §26.3
// reaches a package's class through `p::C`, so the operand of `p::C::m` is
// itself a scope resolution of two identifiers. Answers the key under which
// SimContext holds the class for either shape, or an empty view for another.
static std::string_view ScopedClassKey(const Expr* scope, Arena& arena) {
  if (!scope) return {};
  if (scope->kind == ExprKind::kIdentifier) return scope->text;
  if (scope->kind != ExprKind::kMemberAccess || !scope->is_scope_resolution)
    return {};
  if (!scope->lhs || scope->lhs->kind != ExprKind::kIdentifier) return {};
  if (!scope->rhs || scope->rhs->kind != ExprKind::kIdentifier) return {};
  auto* key = arena.Create<std::string>(std::string(scope->lhs->text) +
                                        "::" + std::string(scope->rhs->text));
  return *key;
}

static bool ResolveClassScope(const Expr* expr, SimContext& ctx, Arena& arena,
                              ClassScopeInfo& info) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  info.access = expr->lhs;
  info.class_name = ScopedClassKey(info.access->lhs, arena);
  if (info.class_name.empty()) return false;
  if (!info.access->rhs || info.access->rhs->kind != ExprKind::kIdentifier)
    return false;
  info.cls = ctx.FindClassType(info.class_name);
  if (!info.cls) return false;
  auto it = info.cls->methods.find(std::string(info.access->rhs->text));
  if (it == info.cls->methods.end()) return false;
  info.method = it->second;
  info.is_void = (info.method->return_type.kind == DataTypeKind::kVoid);
  return true;
}

// Computes the width of a class method's return variable, evaluating the
// declared return type with the parameterized class's bound parameters in scope
// when available. Falls back to 32 bits when the width is indeterminate.
static uint32_t ComputeMethodReturnWidth(ModuleItem* method, SimContext& ctx,
                                         const ClassTypeInfo* param_cls) {
  if (param_cls && param_cls->decl) {
    ScopeMap scope;
    for (const auto& [pname, pexpr] : param_cls->decl->params) {
      auto* var = ctx.FindVariable(pname);
      if (var) scope[pname] = static_cast<int64_t>(var->value.ToUint64());
    }
    uint32_t width = EvalTypeWidth(method->return_type, {}, scope);
    // Not DeclaredTypeWidth here: that asks the one-argument EvalTypeWidth,
    // which would drop the bound parameters `scope` carries and so mis-size a
    // return type whose dimensions name one. Resolve a typedef name against the
    // same table DeclaredTypeWidth uses, but only once the scope-aware overload
    // has had its say.
    if (width == 0) width = ctx.FindTypeWidth(method->return_type.type_name);
    return width == 0 ? 32 : width;
  }
  uint32_t width = DeclaredTypeWidth(method->return_type, ctx);
  return width == 0 ? 32 : width;
}

void ExecClassMethod(ClassMethodTarget target, const Expr* expr,
                     SimContext& ctx, Arena& arena, Logic4Vec& out) {
  ModuleItem* method = target.method;
  bool is_void = (method->return_type.kind == DataTypeKind::kVoid);
  BindFunctionArgs(method, expr, ctx, arena);
  Variable dummy_ret;
  Variable* ret_var = &dummy_ret;
  if (!is_void) {
    // §6.11.3: a method's return type decides the signedness of the variable
    // that holds its result, exactly as a plain function's does in
    // EvalFunctionCall below.
    ret_var = ctx.CreateLocalVariable(
        method->name, ComputeMethodReturnWidth(method, ctx, target.param_cls),
        DeclaredTypeIsSigned(method->return_type, ctx));
    // §13.4.1 gives the implicit variable the method's return type, so §6.11.2
    // decides whether it holds unknowns as it does for any other object.
    ret_var->is_4state = DeclaredTypeIs4State(method->return_type);
  }
  ExecFunctionBody(method, ret_var, ctx, arena);
  out = is_void ? MakeLogic4VecVal(arena, 1, 0) : ret_var->value;
}

static bool TryEvalClassScopeCall(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  ClassScopeInfo info;
  if (!ResolveClassScope(expr, ctx, arena, info)) return false;
  if (!info.access->lhs->elements.empty()) return false;

  if (info.access->rhs->text == "new") {
    out = EvalClassNew(info.class_name, expr, ctx, arena, expr->range.start);
    return true;
  }
  ctx.PushScope();
  // §8.10: a static method can directly call static methods and access static
  // properties of the same class, so the class scope must be in effect while
  // the method body executes for unqualified same-class references to resolve.
  if (info.method->is_static) {
    ctx.PushMethodClass(info.cls);
  }
  ExecClassMethod({info.method}, expr, ctx, arena, out);
  if (info.method->is_static) {
    ctx.PopMethodClass();
  }
  // §13.5.2: output and inout arguments are copied back to the caller on
  // return. The instance-method path does this; the class-scope static path
  // must too, or `Cls::task(out_arg)` silently drops its results. The actual
  // is the caller's expression, so the copy-out runs with the caller's class
  // in force rather than the callee's: a property of the caller's object named
  // as the actual is written against the class declaring it (§8.15), where
  // under the callee's class it landed on the unscoped key alone.
  WritebackOutputArgs(info.method, expr, ctx, arena);
  ctx.PopScope();
  return true;
}

static bool TryEvalParameterizedScopeCall(const Expr* expr, SimContext& ctx,
                                          Arena& arena, Logic4Vec& out) {
  ClassScopeInfo info;
  if (!ResolveClassScope(expr, ctx, arena, info)) return false;
  if (info.access->lhs->elements.empty()) return false;
  ctx.PushScope();
  BindClassParams(info.cls, info.access->lhs, ctx, arena);

  if (info.access->rhs->text == "new") {
    out = EvalClassNew(info.class_name, expr, ctx, arena, expr->range.start);
    ctx.PopScope();
    return true;
  }
  ExecClassMethod({info.method, info.cls}, expr, ctx, arena, out);
  // §13.5.2: copy output/inout arguments back to the caller on return (the
  // parameterized class-scope path, e.g. `Cls#(N)::task(out_arg)`).
  WritebackOutputArgs(info.method, expr, ctx, arena);
  ctx.PopScope();
  return true;
}

bool TryEvalTypedConstructorNew(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  if (!expr || expr->kind != ExprKind::kMemberAccess) return false;
  if (!expr->is_scope_resolution) return false;
  if (!expr->lhs || expr->lhs->kind != ExprKind::kIdentifier) return false;
  if (!expr->rhs || expr->rhs->kind != ExprKind::kIdentifier) return false;
  if (expr->rhs->text != "new") return false;
  auto* cls = ctx.FindClassType(expr->lhs->text);
  if (!cls) return false;
  // §8.25: a parameterized scope (E#(.N(77))::new) carries its specialization
  // overrides in the base identifier's elements; bind them as locals in a fresh
  // scope before constructing, mirroring the procedural assignment path.
  bool parameterized = !expr->lhs->elements.empty();
  if (parameterized) {
    ctx.PushScope();
    BindClassParams(cls, expr->lhs, ctx, arena);
  }
  out = EvalClassNew(expr->lhs->text, nullptr, ctx, arena, expr->range.start);
  if (parameterized) ctx.PopScope();
  return true;
}

static bool TryEvalWeakRefMethodCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (ctx.GetVariableClassType(parts.var_name) != "weak_reference")
    return false;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return false;
  auto wr_handle = var->value.ToUint64();
  auto* wr = ctx.FindWeakReferenceByHandle(wr_handle);
  if (parts.method_name == "get") {
    uint64_t referent = (wr != nullptr) ? wr->Get() : kNullClassHandle;
    out = MakeLogic4VecVal(arena, 64, referent);
    return true;
  }
  if (parts.method_name == "clear") {
    if (wr != nullptr) wr->Clear();
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  return false;
}

static bool TryEvalWeakRefStaticCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  auto* access = expr->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return false;
  if (access->lhs->text != "weak_reference") return false;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return false;
  if (access->rhs->text != "get_id") return false;
  if (expr->args.empty()) return false;
  uint64_t obj_handle = EvalExpr(expr->args[0], ctx, arena).ToUint64();
  int64_t id = WeakReference::GetId(obj_handle);
  out = MakeLogic4VecVal(arena, 64, static_cast<uint64_t>(id));
  return true;
}

static bool TryBuiltinMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  if (TryEvalSemaphoreMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalProcessMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalEventTriggeredCall(expr, ctx, arena, out)) return true;
  if (TryEvalWeakRefMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalEnumMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalStringMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalArrayMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalClassArrayMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalQueueMethodCall(expr, ctx, arena, out)) return true;
  return TryEvalAssocMethodCall(expr, ctx, arena, out);
}

// Clause 18: the randomization methods are built in on any class handle and are
// never user-declared -- randomize() and srandom() (18.6.3, 18.13.3), the
// randstate accessors (18.13.4, 18.13.5), and the constraint_mode()/rand_mode()
// controls (18.9, 18.8) -- so each is dispatched ahead of the user-method
// lookup. 18.12 adds the scope randomize, std::randomize(...) or the bare
// randomize(...) spelling outside a class method, which randomizes the current
// scope's variables rather than a class object's members; it has no receiver,
// so the class randomize path passes it over.
static bool TryDispatchRandomizeMethod(const Expr* expr, SimContext& ctx,
                                       Arena& arena, Logic4Vec& out) {
  if (TryEvalRandomizeMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalScopeRandomizeCall(expr, ctx, arena, out)) return true;
  if (TryEvalObjectSrandom(expr, ctx, arena, out)) return true;
  if (TryEvalObjectGetRandState(expr, ctx, arena, out)) return true;
  if (TryEvalObjectSetRandState(expr, ctx, arena, out)) return true;
  if (TryEvalObjectConstraintMode(expr, ctx, arena, out)) return true;
  return TryEvalObjectRandMode(expr, ctx, arena, out);
}

static bool TryDispatchMethodOrLet(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  if (TryBuiltinMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalSuperMethodCall(expr, ctx, arena, out)) return true;
  if (TryDispatchRandomizeMethod(expr, ctx, arena, out)) return true;
  if (TryEvalClassMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalWeakRefStaticCall(expr, ctx, arena, out)) return true;
  if (TryEvalProcessStaticCall(expr, ctx, arena, out)) return true;
  if (TryEvalClassScopeCall(expr, ctx, arena, out)) return true;
  if (TryEvalParameterizedScopeCall(expr, ctx, arena, out)) return true;
  // §8.10: an unqualified call inside a static method resolves against the
  // enclosing class's static methods before module-level functions.
  if (TryEvalEnclosingStaticCall(expr, ctx, arena, out)) return true;
  // §8.13: and an unqualified call inside an instance method resolves against
  // the enclosing class and the classes it inherits from, ahead of the same
  // module-level names.
  if (TryEvalEnclosingInstanceCall(expr, ctx, arena, out)) return true;
  auto* let_decl = ctx.FindLetDecl(expr->callee);
  if (let_decl) {
    out = EvalLetExpansion(let_decl, expr, ctx, arena);
    return true;
  }
  return false;
}

Logic4Vec EvalFunctionCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec result;
  if (TryDispatchMethodOrLet(expr, ctx, arena, result)) return result;

  auto* func = ctx.FindFunction(expr->callee);
  if (!func) return EvalDpiCall(expr, ctx, arena);

  bool is_static = func->is_static && !func->is_automatic;
  bool is_void = (func->return_type.kind == DataTypeKind::kVoid);

  if (is_static) {
    ctx.PushStaticScope(func->name);
  } else {
    ctx.PushScope();
  }

  ctx.PushQueueRefFrame();
  ctx.PushAssocRefFrame();
  BindFunctionArgs(func, expr, ctx, arena);

  Variable dummy_ret;
  Variable* ret_var = &dummy_ret;
  if (!is_void) {
    auto* existing = is_static ? ctx.FindLocalVariable(func->name) : nullptr;
    uint32_t ret_width = DeclaredTypeWidth(func->return_type, ctx);
    if (ret_width == 0) ret_width = 32;
    // §6.11.3: `byte`, `shortint`, `int`, `integer` and `longint` default to
    // signed, and an explicit `signed`/`unsigned` settles the rest, so the
    // implicit variable that holds the result takes the return type's declared
    // signedness. Built from the width alone it would be unsigned whatever the
    // function returns, and §21.2.1.2's automatic %d field would then lose the
    // sign column an `integer` result is entitled to.
    bool ret_signed = DeclaredTypeIsSigned(func->return_type, ctx);
    ret_var = existing
                  ? existing
                  : ctx.CreateLocalVariable(func->name, ret_width, ret_signed);
    // §13.4.1 with §6.11.2, as above. Set on the retained cell of a static
    // function as well as on a fresh one, so the second call answers as the
    // first did.
    ret_var->is_4state = DeclaredTypeIs4State(func->return_type);
  }

  // §20.17.2: a function body is a calling context on the $stacktrace chain,
  // so record its frame just as task calls do (see PushTaskCallScope).
  ctx.PushFuncName(func->name);
  // §21.2.1.5: a function is a subroutine level of the hierarchical name, so
  // %m inside its body names the function; task calls push the same scope in
  // ExecInlineTaskCall.
  ctx.PushActiveNamedScope(func->name);
  ctx.EnterFunction();
  ExecFunctionBody(func, ret_var, ctx, arena);
  ctx.ExitFunction();
  ctx.PopActiveNamedScope();
  ctx.PopFuncName();
  WritebackOutputArgs(func, expr, ctx, arena);
  WritebackQueueRefs(ctx);
  WritebackAssocRefs(ctx);
  result = is_void ? MakeLogic4VecVal(arena, 1, 0) : ret_var->value;

  if (is_static) {
    ctx.PopStaticScope(func->name);
  } else {
    ctx.PopScope();
  }
  return result;
}

static void PushTaskCallScope(const ModuleItem* func, SimContext& ctx) {
  bool is_static = func->is_static && !func->is_automatic;
  if (is_static) {
    ctx.PushStaticScope(func->name);
  } else {
    ctx.PushScope();
  }
  ctx.PushQueueRefFrame();
  ctx.PushAssocRefFrame();
  ctx.PushFuncName(func->name);
}

static const ModuleItem* SetupTaskCallFromIdentifier(const Expr* expr,
                                                     SimContext& ctx,
                                                     Arena& arena) {
  auto* func = ctx.FindFunction(expr->text);
  if (!func) return nullptr;
  bool is_task = func->kind == ModuleItemKind::kTaskDecl;
  bool is_void_func = func->kind == ModuleItemKind::kFunctionDecl &&
                      func->return_type.kind == DataTypeKind::kVoid;
  if (!is_task && !is_void_func) return nullptr;

  PushTaskCallScope(func, ctx);
  if (is_void_func) ctx.EnterFunction();
  if (!func->func_args.empty()) BindFunctionArgs(func, expr, ctx, arena);
  return func;
}

const ModuleItem* SetupTaskCall(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (!expr) return nullptr;

  if (expr->kind == ExprKind::kIdentifier) {
    return SetupTaskCallFromIdentifier(expr, ctx, arena);
  }
  if (expr->kind != ExprKind::kCall) return nullptr;
  auto* func = ctx.FindFunction(expr->callee);
  if (!func || func->kind != ModuleItemKind::kTaskDecl) return nullptr;

  PushTaskCallScope(func, ctx);
  BindFunctionArgs(func, expr, ctx, arena);
  return func;
}

void TeardownTaskCall(const ModuleItem* func, const Expr* expr, SimContext& ctx,
                      Arena& arena) {
  WritebackOutputArgs(func, expr, ctx, arena);
  WritebackQueueRefs(ctx);
  WritebackAssocRefs(ctx);
  bool is_void_func = func->kind == ModuleItemKind::kFunctionDecl &&
                      func->return_type.kind == DataTypeKind::kVoid;
  if (is_void_func) ctx.ExitFunction();
  ctx.PopFuncName();
  bool is_static = func->is_static && !func->is_automatic;
  if (is_static) {
    ctx.PopStaticScope(func->name);
  } else {
    ctx.PopScope();
  }
}

void ValidateRefLifetime(const ModuleItem* func, DiagEngine& diag) {
  if (!func) return;
  bool is_static = func->is_static && !func->is_automatic;
  if (!is_static) return;
  for (const auto& arg : func->func_args) {
    // §13.5.2: pass-by-reference is illegal in a static-lifetime subroutine,
    // except for a `ref static` argument, which is explicitly permitted.
    if (arg.direction == Direction::kRef && !arg.is_ref_static) {
      diag.Error(func->loc,
                 "ref argument '" + std::string(arg.name) +
                     "' not allowed in static subroutine '" +
                     std::string(func->name) + "'",
                 Subclause("13.5.2"));
    }
  }
}

static std::string_view GetLhsRootName(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  if (e->kind == ExprKind::kSelect && e->base) return GetLhsRootName(e->base);
  if (e->kind == ExprKind::kMemberAccess && e->lhs)
    return GetLhsRootName(e->lhs);
  return {};
}

static void CheckConstRefWrites(
    const Stmt* stmt,
    const std::unordered_set<std::string_view>& const_ref_names,
    const ModuleItem* func, DiagEngine& diag) {
  if (!stmt) return;
  switch (stmt->kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
    case StmtKind::kAssign:
    case StmtKind::kForce: {
      auto root = GetLhsRootName(stmt->lhs);
      if (!root.empty() && const_ref_names.count(root)) {
        diag.Error(stmt->range.start,
                   "cannot write to const ref argument '" + std::string(root) +
                       "' in subroutine '" + std::string(func->name) + "'",
                   Subclause("13.5.2"));
      }
      break;
    }
    default:
      break;
  }
  for (auto* s : stmt->stmts)
    CheckConstRefWrites(s, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->then_branch, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->else_branch, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->body, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->for_body, const_ref_names, func, diag);
  for (auto* s : stmt->for_inits)
    CheckConstRefWrites(s, const_ref_names, func, diag);
  for (auto* s : stmt->for_steps)
    CheckConstRefWrites(s, const_ref_names, func, diag);
  for (const auto& ci : stmt->case_items)
    CheckConstRefWrites(ci.body, const_ref_names, func, diag);
  for (auto* s : stmt->fork_stmts)
    CheckConstRefWrites(s, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->assert_pass_stmt, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->assert_fail_stmt, const_ref_names, func, diag);
  for (const auto& ri : stmt->randcase_items)
    CheckConstRefWrites(ri.second, const_ref_names, func, diag);
}

void ValidateConstRefWriteProtection(const ModuleItem* func, DiagEngine& diag) {
  if (!func) return;
  std::unordered_set<std::string_view> const_ref_names;
  for (const auto& arg : func->func_args) {
    if (arg.direction == Direction::kRef && arg.is_const) {
      const_ref_names.insert(arg.name);
    }
  }
  if (const_ref_names.empty()) return;
  for (auto* stmt : func->func_body_stmts) {
    CheckConstRefWrites(stmt, const_ref_names, func, diag);
  }
}

}  // namespace delta
