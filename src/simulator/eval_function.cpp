#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>

#include "common/arena.h"
#include "common/diagnostic.h"
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
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_assoc_class_handles.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_class_array_handles.h"
#include "simulator/eval_class_params.h"
#include "simulator/eval_class_scope_types.h"
#include "simulator/eval_function_hier.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

// ClassMethodTarget and the ExecClassMethod prototype live in
// eval_function_internal.h (so eval_static_method.cpp can run a method body
// without a `this`); the definition is below.

// §8.10 lets a static method be called through a handle referring to no
// object: the method is the declared class's, found up its base chain, and it
// runs in that class's scope with no object. §8.4 makes a non-static member
// or a virtual method accessed through a null handle illegal, the result
// indeterminate, and lets an implementation issue an error -- this one does,
// at the call, so that the 0 the call then yields is not read as a valid
// value. True where the static method was found and `info` names it.
static bool ResolveThroughNullHandle(const MethodCallParts& parts,
                                     std::string_view class_type,
                                     SimContext& ctx,
                                     InstanceMethodInfo& info) {
  const ClassTypeInfo* cls = ctx.FindClassType(class_type);
  if (cls == nullptr) return false;
  for (const auto* t = cls; t != nullptr; t = t->parent) {
    auto it = t->methods.find(std::string(parts.method_name));
    if (it == t->methods.end()) continue;
    if (!it->second->is_static_method) break;
    info.method = it->second;
    info.owner = t;
    return true;
  }
  if (!parts.loc.IsValid()) return false;
  ctx.GetDiag().Error(parts.loc,
                      "method '" + std::string(parts.method_name) +
                          "' called through the null handle '" +
                          std::string(parts.var_name) + "'",
                      Subclause("8.4"));
  return false;
}

// Whether the class `defining` declares `name` with the virtual qualifier, as
// a pure virtual method or as an `:extends` override, read off the
// declaration for a class whose vtable was never built, a nested one.
static bool DeclarationIsVirtual(const ClassTypeInfo* defining,
                                 std::string_view name) {
  if (defining == nullptr || defining->decl == nullptr) return false;
  for (const auto* m : defining->decl->members) {
    if (m->kind != ClassMemberKind::kMethod || m->method == nullptr ||
        m->method->name != name) {
      continue;
    }
    return m->is_virtual || m->is_pure_virtual || m->method->is_method_extends;
  }
  return false;
}

// §8.20: a method is virtual from the class that first declares it so
// downward -- a virtual method overrides in every base class, a non-virtual
// one in its own class and its descendants alone. A handle's declared class
// therefore sees `name` as virtual only where that class or a base of it has
// put the name in its vtable, or declares it virtual itself; where none has,
// the call is the declared class's own method, whatever a class below it
// later redeclares virtual and so put in the object's vtable. An
// interface-class handle has no such declaration and resolves by the object
// (§8.26.9).
static ModuleItem* ResolveNonVirtualFromDeclared(std::string_view method_name,
                                                 const ClassTypeInfo* declared,
                                                 InstanceMethodInfo& info) {
  if (declared == nullptr || declared->is_interface) return nullptr;
  if (declared->FindVTableIndex(method_name) >= 0) return nullptr;
  const ClassTypeInfo* defining = nullptr;
  ModuleItem* method =
      info.obj->ResolveMethodForType(method_name, declared, &defining);
  if (method == nullptr || DeclarationIsVirtual(defining, method_name))
    return nullptr;
  info.owner = defining;
  return method;
}

bool ResolveMethodByDeclaredClass(ClassObject* obj,
                                  std::string_view declared_class,
                                  std::string_view method_name, SimContext& ctx,
                                  InstanceMethodInfo& info) {
  info.obj = obj;
  if (obj == nullptr) return false;
  auto* declared_type = ctx.FindClassType(declared_class);
  info.method = ResolveNonVirtualFromDeclared(method_name, declared_type, info);
  if (!info.method)
    info.method = info.obj->ResolveVirtualMethod(method_name, &info.owner);
  if (!info.method) {
    // §8.26.9: a non-interface declared type resolves against that type; an
    // interface-class declared type (or no declared type at all) resolves via
    // the object's dynamic type (the implementing class).
    const ClassTypeInfo* from = (declared_type && !declared_type->is_interface)
                                    ? declared_type
                                    : info.obj->type;
    info.method =
        info.obj->ResolveMethodForType(method_name, from, &info.owner);
  }
  return info.method != nullptr;
}

// §8.11: `this` names the object the method was invoked on, so `this.m(...)`
// is the bare `m(...)` written with its receiver, and §13.4.2 lets the method
// -- automatic, as every class method is -- reach itself that way. It is
// resolved as TryEvalEnclosingInstanceCall (eval_static_method.cpp) resolves
// the bare name: the object's dynamic type through the vtable first (§8.20),
// then a walk from the lexically enclosing class up its base chain. `this` is
// a keyword and names no variable, so the handle path below, which reads the
// declared class of a variable, found no class for it and the call fell
// through to the module's functions, answering 0 -- every `this.fib(n - 2)`
// of `fib(n - 1) + this.fib(n - 2)` read 0 and `h.fib(10)` summed to 1.
static bool ResolveMethodOnThis(std::string_view method_name, SimContext& ctx,
                                InstanceMethodInfo& info) {
  ClassObject* self = ctx.CurrentThis();
  if (self == nullptr) return false;
  info.obj = self;
  info.method = self->ResolveVirtualMethod(method_name, &info.owner);
  if (info.method == nullptr) {
    const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
    info.method = self->ResolveMethodForType(
        method_name, enclosing != nullptr ? enclosing : self->type,
        &info.owner);
  }
  return info.method != nullptr;
}

// The handle the property `name` holds on `self`, read as GetPropertyForType
// reads it -- the slot of the class `enclosing` or of a base of it first
// (§8.15), the bare slot or a static one after -- but without the value a
// property never written is made up as, which is no handle.
static uint64_t HeldPropertyHandle(const ClassObject* self,
                                   const ClassTypeInfo* enclosing,
                                   std::string_view name) {
  for (const auto* t = enclosing; t != nullptr; t = t->parent) {
    auto it =
        self->properties.find(std::string(t->name) + "::" + std::string(name));
    if (it != self->properties.end()) return it->second.ToUint64();
  }
  auto it = self->properties.find(std::string(name));
  if (it != self->properties.end()) return it->second.ToUint64();
  // §8.13 (printed 189-190): a base's static handle is the derived object's
  // too, read from the declaring class's one storage; D's own read null.
  const ClassTypeInfo* declarer =
      self->type ? self->type->StaticPropertyDeclarer(name) : nullptr;
  if (declarer == nullptr) return kNullClassHandle;
  return declarer->static_properties.find(std::string(name))->second.ToUint64();
}

// §8.11 with §8.6: a call through a property of the running method's object,
// `obj.get()` with `obj` a class-typed property named without `this.`, runs
// the method on the object the property refers to, resolved by the property's
// declared class as a call through a variable is by the variable's; and
// §8.25 lets that class be named by a type parameter of the enclosing class,
// `T obj`, which PropertyClassName reads through the object's specialization.
// A local of the name shadows the property and takes the variable path. The
// variable path alone answered a call, so one through a property fell to the
// module's functions and read 0 whatever the object held.
static bool ResolveMethodOnPropertyHandle(const MethodCallParts& parts,
                                          SimContext& ctx,
                                          InstanceMethodInfo& info) {
  ClassObject* self = ctx.CurrentThis();
  if (self == nullptr || NameDenotesVariable(parts.var_name, ctx)) return false;
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  if (enclosing == nullptr) enclosing = self->type;
  std::string_view declared =
      PropertyClassName(self, enclosing, parts.var_name, ctx);
  if (declared.empty()) return false;
  uint64_t handle = HeldPropertyHandle(self, enclosing, parts.var_name);
  if (handle == kNullClassHandle) {
    return ResolveThroughNullHandle(parts, declared, ctx, info);
  }
  return ResolveMethodByDeclaredClass(ctx.GetClassObject(handle), declared,
                                      parts.method_name, ctx, info);
}

// §8.3 (printed page 180) makes a variable of a class type a handle, and
// §7.10 (printed 169) and §7.8 give a queue and an associative array declared
// with the class's name, `C q[$]` or `C m[string]`, methods of their own: such
// a variable is an array of handles and no handle. The class record is entered
// under the array's key as under a scalar's (LowerVar in lowerer_var.cpp,
// RegisterPackageClassVariables for a package's), so the record alone cannot
// tell the two apart; the object the key holds can.
static bool NameDenotesArrayOfHandles(std::string_view name, SimContext& ctx) {
  return ctx.FindQueue(name) != nullptr || ctx.FindAssocArray(name) != nullptr;
}

bool ResolveInstanceMethod(const MethodCallParts& parts, SimContext& ctx,
                           InstanceMethodInfo& info) {
  if (parts.var_name == "this")
    return ResolveMethodOnThis(parts.method_name, ctx, info);
  auto class_type = ctx.GetVariableClassType(parts.var_name);
  if (class_type.empty()) {
    return ResolveMethodOnPropertyHandle(parts, ctx, info);
  }
  // A statement's `p1::q.push_back(c1)` is resolved here ahead of the queue
  // path -- ExecInlineTaskCall (stmt_exec.cpp) asks SetupInstanceTaskCall
  // before ExecCallStmtExpr reaches TryBuiltinMethodCall, where the same call
  // in a function body reaches the queue first -- so the carrier's 0 was read
  // as a null handle and §8.4's error reported for a queue that held handles.
  if (NameDenotesArrayOfHandles(parts.var_name, ctx)) return false;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return false;
  auto handle = var->value.ToUint64();
  if (handle == kNullClassHandle) {
    return ResolveThroughNullHandle(parts, class_type, ctx, info);
  }
  return ResolveMethodByDeclaredClass(ctx.GetClassObject(handle), class_type,
                                      parts.method_name, ctx, info);
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
  // §8.7/§8.15: the `super.new(...)` that opens a constructor body is the
  // base constructor call the construction of the object has already made,
  // with these arguments, before this body began (EvalClassNew in
  // eval_class_new.cpp), and §8.17's `super.new(default)` forwarded the
  // expanded actuals the same way; reaching the statement runs nothing more,
  // where running the base constructor a second time ran it once with no
  // arguments first -- uvm_component::new saw the name "" instead of
  // "__top__" and built a second root.
  if (parts.method_name == "new" && IsSuperNewRunByConstruction(expr, ctx)) {
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

Logic4Vec RunInstanceMethod(const InstanceMethodInfo& info, const Expr* expr,
                            SimContext& ctx, Arena& arena) {
  Logic4Vec out;
  // §8.10/§8.9: a static method invoked through an instance handle shares the
  // class's single static storage; dispatch it in class scope (no `this`).
  if (info.method->is_static_method) {
    const ClassTypeInfo* scope =
        info.obj != nullptr ? info.obj->type : info.owner;
    RunStaticMethodInClassScope({info.method, scope}, expr, ctx, arena, out);
    return out;
  }
  // Run the body with its defining class as the enclosing scope so an
  // unqualified member resolves to that level even when a derived class
  // shadows the name (§8.15).
  ctx.PushMethodClass(info.owner);
  out = ExecInstanceMethodCall(info.method, info.obj, expr, ctx, arena);
  ctx.PopMethodClass();
  return out;
}

// §26.3 admits a package-qualified handle as the receiver, `p1::h.m(...)`,
// resolved by the key ExtractHandleMethodCallParts answers.
static bool TryEvalClassMethodCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractHandleMethodCallParts(expr, arena, parts)) return false;
  InstanceMethodInfo info;
  if (!ResolveInstanceMethod(parts, ctx, info)) return false;
  out = RunInstanceMethod(info, expr, ctx, arena);
  return true;
}

void BindClassParams(const ClassTypeInfo* cls, const Expr* base_id,
                     SimContext& ctx, Arena& arena) {
  if (!cls->decl) return;
  const auto& params = cls->decl->params;
  const auto& values = base_id->elements;
  // §8.25 with §6.20.2: the actual or the default is sized by the
  // parameter's declared type (ClassParamSizer).
  ClassParamSizer sizer(cls->decl);
  for (size_t i = 0; i < params.size(); ++i) {
    Logic4Vec val;
    if (i < values.size()) {
      val = sizer.Value(i, values[i], ctx, arena);
    } else if (params[i].second) {
      val = sizer.Value(i, params[i].second, ctx, arena);
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
std::string_view ScopedClassKey(const Expr* scope, Arena& arena) {
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
    if (width != 0) return width;
  }
  uint32_t width = DeclaredTypeWidth(method->return_type, ctx);
  return width == 0 ? 32 : width;
}

// §13.4.1 with §6.16: the value a call answers -- a placeholder for a void
// subroutine, else the implicit variable's, carrying the string kind
// ShapeStringReturnVariable gave the variable of a subroutine declared to
// return a string, so that a method called on the call, `h.get().len()`,
// reads it as text (TryEvalCallResultMethodCall); the words alone read as a
// packed number and no string method reached them.
static Logic4Vec CallResult(bool is_void, const Variable* ret_var,
                            Arena& arena) {
  if (is_void) return MakeLogic4VecVal(arena, 1, 0);
  Logic4Vec result = ret_var->value;
  result.is_string = ret_var->is_string;
  return result;
}

void ExecClassMethod(ClassMethodTarget target, const Expr* expr,
                     SimContext& ctx, Arena& arena, Logic4Vec& out) {
  ModuleItem* method = target.method;
  bool is_void = (method->return_type.kind == DataTypeKind::kVoid);
  BindFunctionArgs(method, expr, ctx, arena);
  // §26.2 with §8.24: a method of a class a package declares, in-class or
  // out-of-block, reads the package's parameters, enum literals, variables
  // and functions by their bare names, so its frame -- the one the caller
  // pushed for the call -- carries the package RecordClassPackage
  // (lowerer_class.cpp) recorded, given once the actuals are bound so that
  // a caller's actual of a package variable's name still reads the caller's.
  // §23.9: the frame is the method body's own scope from here, so a body
  // with no package of its own reads none of its caller's.
  ctx.EnterSubroutineScope(ctx.SubroutinePackage(method));
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
    // §13.4.1 with §6.12: a method returning real holds its result in a real
    // variable, as EvalFunctionCall's below does; a `return i` of an integer
    // then converts under §6.12.1 (ExecFuncReturn) rather than handing out
    // the integer's bits as a double.
    ret_var->is_real = DeclaredTypeIsReal(method->return_type, ctx);
  }
  ExecFunctionBody(method, ret_var, ctx, arena);
  out = CallResult(is_void, ret_var, arena);
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
  if (info.method->is_static_method) {
    ctx.PushMethodClass(info.cls);
  }
  ExecClassMethod({info.method}, expr, ctx, arena, out);
  if (info.method->is_static_method) {
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
  // §8.25.1: the type actuals of the specialization the call names, bound
  // in the same frame for $bits(T) and the like inside the static body.
  BindClassScopeTypeActuals(info.cls->decl, info.access->lhs, ctx, arena);

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

// §8.30.3 and §8.30.4: get() and clear() on a weak_reference variable. §26.3
// admits a package's variable as the receiver, `p::w.get()`, by the "p.w" key
// ExtractHandleMethodCallParts answers; taken as an identifier alone, the
// scoped call resolved no reference and answered nothing.
static bool TryEvalWeakRefMethodCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractHandleMethodCallParts(expr, arena, parts)) return false;
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
  if (TryEvalMailboxMethodCall(expr, ctx, arena, out)) return true;
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
  // §8.6: a method called on a method call's result, `c.some_method(7).who()`,
  // runs on the object the first call returned; ExtractMethodCallParts above
  // takes a variable alone for the handle side.
  if (TryEvalCallResultMethodCall(expr, ctx, arena, out)) return true;
  // §7.8/§8.4 with §8.6: and one called on an element of a container of
  // handles, `arr[0].f()`, `q[0].f()` or `m["a"].f()`, runs on its object.
  if (TryEvalElementObjectMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalAssocElementMethodCall(expr, ctx, arena, out)) return true;
  // and one on a chained property receiver, `c.kid.f()`, on its object.
  if (TryEvalMethodOnEvaluatedBase(expr, ctx, arena, out)) return true;
  if (TryEvalWeakRefStaticCall(expr, ctx, arena, out)) return true;
  if (TryEvalProcessStaticCall(expr, ctx, arena, out)) return true;
  if (TryEvalClassScopeCall(expr, ctx, arena, out)) return true;
  if (TryEvalParameterizedScopeCall(expr, ctx, arena, out)) return true;
  // §8.10 with §8.13: an unqualified call inside a static method resolves
  // against the static methods of the enclosing class and of the classes it
  // inherits from, before module-level functions.
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

  // §13.3 with §23.6: a function called by hierarchical name, `u1.f(2)`,
  // is the instance's, and its body runs there (eval_function_hier.h).
  SubroutineTarget target = FindSubroutineTarget(expr, ctx, arena);
  const ModuleItem* func = target.func;
  if (!func) return EvalDpiCall(expr, ctx, arena);

  bool is_static = func->is_static && !func->is_automatic;
  bool is_void = (func->return_type.kind == DataTypeKind::kVoid);

  // §13.3.2 with §23.6: the frame is pushed with the process standing in
  // the callee's instance, so a static function's frame is that instance's.
  EnterCalleeInstance(ctx, target);
  if (is_static) {
    ctx.PushStaticScope(func->name);
  } else {
    ctx.PushScope();
  }
  // §26.3 with §13.4: a package function's frame carries its package, so its
  // body and its default actuals read the package's variables by their bare
  // names; the caller's actuals are read with the frame set aside
  // (ResolveArgValue) and see the caller's scope. §23.9: the frame is the
  // body's own scope, so a function with no package reads none of its
  // caller's body import.
  ctx.EnterSubroutinePackage(func);
  // §27.4: a generate block instance's function reads its loop index.
  BindGenBlockConsts(target, ctx, arena);

  ctx.PushQueueRefFrame();
  ctx.PushAssocRefFrame();
  BindActualsInCaller(func, expr, ctx, arena);

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
    // §13.4.1 with §6.12: the implicit variable of a function returning real,
    // shortreal or realtime is a real variable, so the store a `return`
    // makes into it and the `f = expr` form alike convert under §6.12.1, and
    // the value the caller reads is a real. Left at the default, `return i`
    // of an int local handed the caller the integer's bits, which %f read as
    // 0.0.
    ret_var->is_real = DeclaredTypeIsReal(func->return_type, ctx);
  }

  // §20.17.2: a function body is a calling context on the $stacktrace chain,
  // so record its frame just as task calls do (see PushTaskCallScope).
  ctx.PushFuncName(func->name);
  // §21.2.1.5: a function is a subroutine level of the hierarchical name, so
  // %m inside its body names the function; task calls push the same scope in
  // ExecInlineTaskCall.
  ctx.PushActiveNamedScope(func->name);
  ctx.EnterFunction();
  ExecFunctionBodyInCallee(func, target.inst_prefix, ret_var, ctx, arena);
  ctx.ExitFunction();
  ctx.PopActiveNamedScope();
  ctx.PopFuncName();
  WritebackInCaller(func, expr, ctx, arena);
  result = CallResult(is_void, ret_var, arena);

  if (is_static) {
    ctx.PopStaticScope(func->name);
  } else {
    ctx.PopScope();
  }
  LeaveCalleeInstance(ctx);
  return result;
}

// §13.3 with §23.6: the process stands in the callee's instance from here
// until TeardownTaskCall, across every timing control of the body, so the
// static frame is the instance's own (§13.3.2) and a bare name the body reads
// is the instance's variable; the actuals are read in the enabling instance
// (BindActualsInCaller). A bare enable stands where it was, its target the
// enabling instance's.
static void PushTaskCallScope(const SubroutineTarget& target, SimContext& ctx,
                              Arena& arena) {
  const ModuleItem* func = target.func;
  EnterCalleeInstance(ctx, target);
  bool is_static = func->is_static && !func->is_automatic;
  if (is_static) {
    ctx.PushStaticScope(func->name);
  } else {
    ctx.PushScope();
  }
  // §27.4: a generate block instance's task reads its loop index.
  BindGenBlockConsts(target, ctx, arena);
  ctx.PushQueueRefFrame();
  ctx.PushAssocRefFrame();
  ctx.PushFuncName(func->name);
}

static const ModuleItem* SetupTaskCallFromIdentifier(const Expr* expr,
                                                     SimContext& ctx,
                                                     Arena& arena) {
  SubroutineTarget target = FindSubroutineTarget(expr, ctx, arena);
  const ModuleItem* func = target.func;
  if (!func) return nullptr;
  bool is_task = func->kind == ModuleItemKind::kTaskDecl;
  bool is_void_func = func->kind == ModuleItemKind::kFunctionDecl &&
                      func->return_type.kind == DataTypeKind::kVoid;
  if (!is_task && !is_void_func) return nullptr;

  PushTaskCallScope(target, ctx, arena);
  if (is_void_func) ctx.EnterFunction();
  if (!func->func_args.empty()) BindActualsInCaller(func, expr, ctx, arena);
  return func;
}

const ModuleItem* SetupTaskCall(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (!expr) return nullptr;

  if (expr->kind == ExprKind::kIdentifier) {
    return SetupTaskCallFromIdentifier(expr, ctx, arena);
  }
  if (expr->kind != ExprKind::kCall) return nullptr;
  SubroutineTarget target = FindSubroutineTarget(expr, ctx, arena);
  const ModuleItem* func = target.func;
  if (!func || func->kind != ModuleItemKind::kTaskDecl) return nullptr;

  PushTaskCallScope(target, ctx, arena);
  BindActualsInCaller(func, expr, ctx, arena);
  return func;
}

void TeardownTaskCall(const ModuleItem* func, const Expr* expr, SimContext& ctx,
                      Arena& arena) {
  WritebackInCaller(func, expr, ctx, arena);
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
  // §13.3 with §23.6: the enable is over, and the process is back in the
  // instance that wrote it (PushTaskCallScope).
  LeaveCalleeInstance(ctx);
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
