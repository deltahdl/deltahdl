// §13.3 with §8.6: a task enabled through an object handle, `h.t(...)`, may
// contain time-controlling statements, so it runs as a coroutine in
// ExecInstanceTaskCall (stmt_exec_class_task.cpp) rather than through the
// synchronous function interpreter ExecClassMethod drives. The frame such a
// call stands in is the one ExecInstanceMethodCall builds -- a scope, `this`,
// the queue and associative reference frames, the defining class as the
// enclosing scope (§8.15) -- and it is set up and torn down here, beside the
// resolution of the handle and the method, so the two callers agree on it.

#include "simulator/eval_instance_task.h"

#include <string>
#include <string_view>
#include <unordered_map>

#include "common/arena.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/eval_assoc_class_handles.h"
#include "simulator/eval_class_array_handles.h"
#include "simulator/eval_class_scope_types.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

// §8.10 with §8.23: a static task named through the class scope, `C::t(...)`
// or `p::C::t(...)`, resolved to the task and the class whose scope it runs
// in; false for any other call. A static task named through a handle,
// `h.t(...)`, resolves through ResolveInstanceMethod as an instance task does,
// the handle standing for the class (§8.10).
static bool ResolveStaticTaskByScope(const Expr* expr, SimContext& ctx,
                                     Arena& arena, InstanceMethodInfo& call) {
  const Expr* access = expr->lhs;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      !access->is_scope_resolution || access->rhs == nullptr ||
      access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  std::string_view class_key = ScopedClassKey(access->lhs, arena);
  if (class_key.empty()) return false;
  const ClassTypeInfo* cls = ctx.FindClassType(class_key);
  if (cls == nullptr) return false;
  auto it = cls->methods.find(std::string(access->rhs->text));
  if (it == cls->methods.end()) return false;
  call.obj = nullptr;
  call.method = it->second;
  call.owner = cls;
  return true;
}

// §26.3: whether `expr` is a package-qualified name, `p1::h`, the scope
// resolution of two identifiers the parser leaves it as.
static bool IsPackageQualifiedName(const Expr* expr) {
  return expr->kind == ExprKind::kMemberAccess && expr->is_scope_resolution &&
         expr->lhs != nullptr && expr->rhs != nullptr &&
         expr->lhs->kind == ExprKind::kIdentifier &&
         expr->rhs->kind == ExprKind::kIdentifier;
}

// §26.3 with §8.6: the handle and the member of the member access `access`,
// the handle by the key its storage and its class record are held under;
// see the declaration in eval_function_internal.h. The identifier handle is
// taken as ExtractMethodCallParts takes it, `C::m` with it, and the scoped
// handle only under a member access that is no scope resolution, so that
// `p::C::m` stays a static-scope call. Taken as an identifier alone,
// `p1::h.m()` and `p1::h.t(5);` resolved no object, so the call ran on none
// and answered 0.
bool ExtractHandleAccessParts(const Expr* access, Arena& arena,
                              MethodCallParts& out) {
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->lhs == nullptr || access->rhs == nullptr ||
      access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  const Expr* handle = access->lhs;
  if (handle->kind == ExprKind::kIdentifier) {
    out.var_name = handle->text;
  } else if (!access->is_scope_resolution && IsPackageQualifiedName(handle)) {
    auto* key = arena.Create<std::string>(std::string(handle->lhs->text) + "." +
                                          std::string(handle->rhs->text));
    out.var_name = *key;
  } else {
    return false;
  }
  out.method_name = access->rhs->text;
  out.loc = access->rhs->range.start;
  return true;
}

bool ExtractHandleMethodCallParts(const Expr* expr, Arena& arena,
                                  MethodCallParts& out) {
  return expr != nullptr && ExtractHandleAccessParts(expr->lhs, arena, out);
}

// §8.13 with §8.20: the method `name` names on the running object, written
// bare inside a method of the object's class -- the object's own class
// through the vtable first, then the walk from the lexically enclosing class
// up its base chain, the two-step the receiver-qualified call takes. False
// outside an instance method.
static bool ResolveMethodOnRunningObject(std::string_view name, SimContext& ctx,
                                         InstanceMethodInfo& call) {
  ClassObject* self = ctx.CurrentThis();
  if (self == nullptr) return false;
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  if (enclosing == nullptr) enclosing = self->type;
  call.obj = self;
  call.method = self->ResolveVirtualMethod(name, &call.owner);
  if (call.method == nullptr) {
    call.method = self->ResolveMethodForType(name, enclosing, &call.owner);
  }
  return call.method != nullptr;
}

// §8.15: `super.m` names the base class's m from inside a derived class, the
// one the derived class overrides included, so the walk starts at the parent
// of the lexically enclosing class and takes no virtual dispatch, which would
// land back on the override. The body runs on the same object. False outside
// an instance method of a derived class.
static bool ResolveMethodThroughSuper(std::string_view name, SimContext& ctx,
                                      InstanceMethodInfo& call) {
  ClassObject* self = ctx.CurrentThis();
  if (self == nullptr) return false;
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  if (enclosing == nullptr) enclosing = self->type;
  if (enclosing == nullptr || enclosing->parent == nullptr) return false;
  call.obj = self;
  call.method =
      self->ResolveMethodForType(name, enclosing->parent, &call.owner);
  return call.method != nullptr;
}

// The method `h.m` names: the base class's through `super` (§8.15), or
// ResolveInstanceMethod's answer for `this` and for a handle.
static bool ResolveMethodByParts(const MethodCallParts& parts, SimContext& ctx,
                                 InstanceMethodInfo& call) {
  if (parts.var_name == "super") {
    return ResolveMethodThroughSuper(parts.method_name, ctx, call);
  }
  return ResolveInstanceMethod(parts, ctx, call);
}

// §8.9 (printed page 186) with §8.6 (printed 183): the method `access` names
// on the object a static property holds a handle to -- `m_inst.add(7)` in a
// static method of the class (§8.10, printed 186), which runs on no object
// for ResolveMethodOnPropertyHandle to read the property through, or
// `C::m_inst.add(7)` from anywhere -- resolved by the class the property is
// declared with, as a call through a variable is by the variable's
// (ResolveMethodByDeclaredClass), which decides §8.20's non-virtual dispatch
// where the object is of a class derived from it. False where the base names
// no static property or the property holds no live object. Asked ahead of
// the general evaluation below, which the bare form never reached: a bare
// name is left to the shaped arms, and with no `this` running they resolved
// nothing, so `m_inst.add(7)` fell to the module's functions and wrote no
// property.
static bool ResolveMethodOnStaticHandle(const Expr* access, SimContext& ctx,
                                        Arena& arena,
                                        InstanceMethodInfo& call) {
  StaticPropertyRef ref;
  if (!ResolveStaticPropertyBase(access->lhs, ctx, arena, ref)) return false;
  std::string_view declared_key;
  ClassObject* obj = StaticPropertyObject(ref, ctx, &declared_key);
  if (obj == nullptr) return false;
  return ResolveMethodByDeclaredClass(obj, declared_key, access->rhs->text, ctx,
                                      call);
}

// §8.6 (printed page 183): an object's task is enabled through any handle to
// it, and a handle is what any expression of a class type yields -- a
// method's result, `c.self().t(...)`, a property of an element's object,
// `arr[0].kid.t(...)`, a static property named through the class scope. The
// method `access` names on the object the access's base evaluates to,
// resolved by the object's own class (ResolveMethodByDeclaredClass with no
// declared class: a virtual method by the object, §8.20, and a non-virtual
// one as the object's class holds it). Asked after the shaped resolvers --
// a named handle (ResolveMethodByParts), an element of a container
// (ResolveElementObjectMethod, ResolveAssocElementMethod) -- and not before
// them, because those know the receiver's declared class, which decides
// §8.20's non-virtual dispatch through a base-class handle and §8.15's
// `super`, and the value alone cannot recover it; a base they decline is
// then evaluated exactly once here. A bare name is left to them outright,
// but for a static property of the running method's class
// (ResolveMethodOnStaticHandle above): a name that holds no object is theirs
// to report (ResolveThroughNullHandle). False for an access of any other
// shape or a base yielding no live object.
// Admitted by shape alone, the enable through such a receiver fell to the
// expression evaluator and ran on the synchronous function interpreter,
// which stepped over the task's `#10` and returned at time 0. The
// expression evaluator's own arm, TryEvalMethodOnEvaluatedBase below,
// resolves a call's receiver through this for the same reasons, in the same
// place after its shaped arms.
static bool ResolveMethodOnEvaluatedBase(const Expr* access, SimContext& ctx,
                                         Arena& arena,
                                         InstanceMethodInfo& call) {
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution || access->lhs == nullptr ||
      access->rhs == nullptr || access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (ResolveMethodOnStaticHandle(access, ctx, arena, call)) return true;
  if (access->lhs->kind == ExprKind::kIdentifier) return false;
  ClassObject* obj =
      ctx.GetClassObject(EvalExpr(access->lhs, ctx, arena).ToUint64());
  return ResolveMethodByDeclaredClass(obj, {}, access->rhs->text, ctx, call);
}

// Whether the receiver `base` is a member path starting at a call,
// `c.self()` or `c.self().kid`, which TryEvalCallResultMethodCall
// (eval_call_result.cpp) owns in the expression evaluator: it evaluates the
// call before it resolves the method, so the evaluator's arm below must not
// evaluate such a base again where that arm declined -- a null result, a
// method the object lacks -- or the call's side effects would run twice.
static bool StartsAtACall(const Expr* base) {
  const Expr* e = base;
  while (e != nullptr && e->kind == ExprKind::kMemberAccess) e = e->lhs;
  return e != nullptr && e->kind == ExprKind::kCall;
}

bool TryEvalMethodOnEvaluatedBase(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  if (expr == nullptr || expr->kind != ExprKind::kCall ||
      expr->lhs == nullptr || expr->lhs->kind != ExprKind::kMemberAccess ||
      StartsAtACall(expr->lhs->lhs)) {
    return false;
  }
  InstanceMethodInfo info;
  if (!ResolveMethodOnEvaluatedBase(expr->lhs, ctx, arena, info)) return false;
  out = RunInstanceMethod(info, expr, ctx, arena);
  return true;
}

// §13.5.5: the method a statement names without the parentheses. `h.m` is a
// member access of a handle and a member, resolved on the handle's object as
// the call `h.m(...)` is, the handle an identifier or, §26.3, a package's
// variable named through the package scope resolution operator, `p1::h.m;`,
// which ExtractHandleAccessParts takes by its "p1.h" key; a bare `m` inside
// an instance method is a method of the running object's class or of one it
// inherits from (§8.13), the override the object's class holds taken first
// (§8.20). False for any other expression, for a member that is a property
// and for a name that is a variable. Taken as two identifiers alone, the
// scoped form read m as a property and discarded the value. An element of a
// container of handles is a handle here as in the parenthesised call
// (§8.6), so `arr[0].run;` is `arr[0].run();`.
static bool ResolveMethodNamedBare(const Expr* expr, SimContext& ctx,
                                   Arena& arena, InstanceMethodInfo& call) {
  MethodCallParts parts;
  if (expr->kind == ExprKind::kMemberAccess && !expr->is_scope_resolution) {
    if (ExtractHandleAccessParts(expr, arena, parts)) {
      return ResolveMethodByParts(parts, ctx, call) ||
             ResolveMethodOnStaticHandle(expr, ctx, arena, call);
    }
    return ResolveElementObjectMethod(expr, ctx, arena, call) ||
           ResolveAssocElementMethod(expr, ctx, arena, call) ||
           ResolveMethodOnEvaluatedBase(expr, ctx, arena, call);
  }
  if (expr->kind != ExprKind::kIdentifier) return false;
  return ResolveMethodOnRunningObject(expr->text, ctx, call);
}

// The method a statement's expression calls on an object: `h.m(...)` through
// the handle, `this.m(...)` and `super.m(...)`, the parenthesis-free forms
// above, or a bare `m(...)` inside a method of the object's class (§8.13).
// §13.3 has a task enable other tasks and return only when they have
// completed, so the bare and the `super` forms are resolved here for the
// coroutine path as the handle form is; left to the expression evaluator,
// `go(d)` and `super.go(d)` inside a class task ran through the synchronous
// function interpreter, which wrote the property and dropped the `#d`, and
// the enable from the initial returned at time 0.
// §26.3 admits a package-qualified handle as the receiver, `p1::h.t(...)`,
// resolved by the key ExtractHandleMethodCallParts answers.
// §8.6 (printed page 183) with §7.4.2, §7.10 and §7.8: an element of a
// declared array, a queue or an associative array of handles is a handle to
// enable through as any other, `arr[0].t(...)`, `q[0].t(...)`,
// `aa["k"].t(...)`, resolved by the element's object
// (ResolveElementObjectMethod, ResolveAssocElementMethod). Admitted as an
// identifier or `p1::h` alone, the enable through an element fell to the
// expression evaluator, which ran the task on the synchronous function
// interpreter: its `#10` was stepped over, the write after it landed at time 0,
// and the enable returned at 0 where §13.3 (printed 336-337) returns it once
// the body has run. Any other base yielding a handle -- a call's result, a
// property of an element's object -- is resolved by the object it evaluates
// to (ResolveMethodOnEvaluatedBase), last.
static bool ResolveMethodOfStatement(const Expr* expr, SimContext& ctx,
                                     Arena& arena, InstanceMethodInfo& call) {
  if (expr->kind != ExprKind::kCall) {
    return ResolveMethodNamedBare(expr, ctx, arena, call);
  }
  if (expr->lhs != nullptr && expr->lhs->kind == ExprKind::kIdentifier &&
      !expr->callee.empty()) {
    return ResolveMethodOnRunningObject(expr->callee, ctx, call);
  }
  MethodCallParts parts;
  if (ExtractHandleMethodCallParts(expr, arena, parts)) {
    return ResolveMethodByParts(parts, ctx, call) ||
           ResolveMethodOnStaticHandle(expr->lhs, ctx, arena, call);
  }
  return ResolveElementObjectMethod(expr->lhs, ctx, arena, call) ||
         ResolveAssocElementMethod(expr->lhs, ctx, arena, call) ||
         ResolveMethodOnEvaluatedBase(expr->lhs, ctx, arena, call);
}

bool SetupInstanceTaskCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           InstanceMethodInfo& call) {
  if (expr == nullptr) return false;
  bool through_handle = ResolveMethodOfStatement(expr, ctx, arena, call);
  if (!through_handle && !ResolveStaticTaskByScope(expr, ctx, arena, call))
    return false;
  if (call.method->kind != ModuleItemKind::kTaskDecl) return false;
  // §8.10: a static task runs in class scope with no `this`, whether named
  // through the class scope or through a handle, and §13.3 lets its body hold
  // timing controls as any task's may, so it is run as a coroutine here too;
  // handed to the synchronous evaluator, its delay was skipped and its fork
  // never joined. `this` is pushed for an instance task alone, and
  // TeardownInstanceTaskCall pops it for that one alone.
  if (call.method->is_static_method) {
    call.obj = nullptr;
  } else if (call.obj == nullptr) {
    return false;
  }
  ctx.PushMethodClass(call.owner);
  ctx.PushScope();
  // §8.25: a static task named through a specialization, `C#(42)::t(...)`,
  // runs with the class's parameters bound to the specialization's actuals,
  // as the evaluator's class-scope call binds them (BindClassParams); a type
  // actual, `C#(byte)::t(...)`, is bound as a type beside them, since a value
  // bind makes a 1-bit local of a type name (BindClassScopeTypeActuals).
  // §8.25.1 with §26.3 admits the package-qualified class as the prefix,
  // `p::C#(byte)::t(...)`, which Parser::ParseParameterizedScope leaves as
  // the `p::C` scope resolution carrying the `#(...)` list, the shape
  // ResolveStaticTaskByScope has already resolved the class from; bound for
  // the bare name alone, that form ran with the class's defaults.
  const Expr* scope = expr->lhs != nullptr ? expr->lhs->lhs : nullptr;
  if (call.obj == nullptr && scope != nullptr && !scope->elements.empty()) {
    BindClassParams(call.owner, scope, ctx, arena);
    BindClassScopeTypeActuals(call.owner, scope, ctx, arena);
  }
  if (call.obj != nullptr) ctx.PushThis(call.obj);
  ctx.PushQueueRefFrame();
  ctx.PushAssocRefFrame();
  // §20.17.2: the task is a calling context on the $stacktrace chain, as a
  // module task enabled by name is through PushTaskCallScope.
  ctx.PushFuncName(call.method->name);
  BindFunctionArgs(call.method, expr, ctx, arena);
  // §26.2: a task of a class a package declares reads the package's names
  // bare, as ExecClassMethod gives a function of the class its package.
  ctx.EnterSubroutineScope(ctx.SubroutinePackage(call.method));
  return true;
}

void TeardownInstanceTaskCall(const InstanceMethodInfo& call, const Expr* expr,
                              SimContext& ctx, Arena& arena) {
  // §13.5: output and inout arguments are copied back to the caller on
  // return, as the instance-method path does. The actual is an expression of
  // the enabling method's, so §8.11 makes a property it names the enabling
  // object's: `b.addt(v, w)` in a task of A names A's `w`. The copy-out is
  // therefore made once the task's `this` and its class are popped, as
  // ExecInstanceMethodCall pops them before its writeback; with B's object
  // still in force the value landed on B's `w` and A's never changed.
  if (call.obj != nullptr) ctx.PopThis();
  ctx.PopMethodClass();
  WritebackOutputArgs(call.method, expr, ctx, arena);
  WritebackQueueRefs(ctx);
  WritebackAssocRefs(ctx);
  ctx.PopFuncName();
  ctx.PopScope();
}

// §13.5.5 (printed page 351): whether a call of `method` may leave off its
// parentheses in an expression -- a function whose formals, if any, all have
// defaults. The constructor is not such a method: `C::new` is answered by
// TryEvalTypedConstructorNew.
static bool CallableWithoutParens(const ModuleItem* method) {
  if (method == nullptr || method->kind != ModuleItemKind::kFunctionDecl ||
      method->name == "new") {
    return false;
  }
  for (const auto& arg : method->func_args) {
    if (arg.default_value == nullptr) return false;
  }
  return true;
}

// The method `cls` declares or inherits (§8.13) under `name`, or nullptr.
static const ModuleItem* MethodOfClassChain(const ClassTypeInfo* cls,
                                            std::string_view name) {
  for (; cls != nullptr; cls = cls->parent) {
    auto it = cls->methods.find(std::string(name));
    if (it != cls->methods.end()) return it->second;
  }
  return nullptr;
}

// The method a name read as a value designates: a bare `m` of the running
// method's class (§8.13), `C::m` or `T::m` through the class scope, a type
// parameter's standing for the class its actual names (§8.23, §8.25), or
// `h.m` through a handle, `this` or `super`, as ResolveMethodNamedBare
// resolves the statement form. Nullptr for a name designating no method.
static const ModuleItem* MethodNamedAsAValue(const Expr* expr, SimContext& ctx,
                                             Arena& arena) {
  if (expr->kind == ExprKind::kIdentifier) {
    const ClassTypeInfo* scope = ctx.CurrentMethodClass();
    if (scope == nullptr && ctx.CurrentThis() != nullptr) {
      scope = ctx.CurrentThis()->type;
    }
    return MethodOfClassChain(scope, expr->text);
  }
  if (expr->kind != ExprKind::kMemberAccess || expr->rhs == nullptr ||
      expr->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  if (expr->is_scope_resolution) {
    std::string_view key = ScopedClassKey(expr->lhs, arena);
    if (key.empty()) return nullptr;
    const ClassTypeInfo* cls = ctx.FindClassType(key);
    if (cls == nullptr) cls = ClassNamedByTypeParam(key, ctx, arena);
    return MethodOfClassChain(cls, expr->rhs->text);
  }
  MethodCallParts parts;
  InstanceMethodInfo call;
  if (!ExtractHandleAccessParts(expr, arena, parts)) return nullptr;
  // Only asking which member the name designates, so a null handle is not
  // reported here (ResolveThroughNullHandle reports at a located call alone):
  // `b.x` naming a property through a null b is the member read's to judge.
  parts.loc = SourceLoc::None();
  if (!ResolveMethodByParts(parts, ctx, call) &&
      !ResolveMethodOnStaticHandle(expr, ctx, arena, call)) {
    return nullptr;
  }
  return call.method;
}

// The call `name()` that a method named without its parentheses stands for,
// shaped as Parser::ParseCallExpr shapes the written call and built once per
// name, so evaluating the name again in a loop allocates nothing more.
static const Expr* ParenFreeCall(const Expr* name, SimContext& ctx) {
  auto [it, fresh] = ctx.ParenFreeCalls().try_emplace(name, nullptr);
  if (fresh) {
    Arena& arena = ctx.GetArena();
    auto* call = arena.Create<Expr>();
    call->kind = ExprKind::kCall;
    call->callee = name->text;
    call->lhs = arena.Create<Expr>(*name);
    call->range = name->range;
    it->second = call;
  }
  return it->second;
}

bool TryEvalParenFreeMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  if (expr == nullptr ||
      !CallableWithoutParens(MethodNamedAsAValue(expr, ctx, arena))) {
    return false;
  }
  out = EvalExpr(ParenFreeCall(expr, ctx), ctx, arena);
  return true;
}

void ExecCallStmtExpr(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr == nullptr) return;
  InstanceMethodInfo call;
  if (ResolveMethodNamedBare(expr, ctx, arena, call)) {
    RunInstanceMethod(call, expr, ctx, arena);
    return;
  }
  EvalExpr(expr, ctx, arena);
}

}  // namespace delta
