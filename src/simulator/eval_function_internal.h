#pragma once

#include <iosfwd>
#include <string_view>

#include "common/types.h"

namespace delta {

struct Expr;
struct ModuleItem;
class SimContext;
class Arena;

// Shared between eval_system_task.cpp and eval_system_func.cpp. The system-task
// helpers are defined once in eval_system_task.cpp; the system-function
// dispatch in eval_system_func.cpp routes to them.
Logic4Vec EvalPrngCall(const Expr* expr, SimContext& ctx, Arena& arena,
                       std::string_view name);
bool IsDisplayOrWriteTask(std::string_view name);
void ExecDisplayWrite(const Expr* expr, SimContext& ctx, Arena& arena);
void ExecSeverityTask(const Expr* expr, SimContext& ctx, Arena& arena,
                      const char* prefix, std::ostream& os);
Logic4Vec EvalDeferredPrint(const Expr* expr, SimContext& ctx, Arena& arena);
bool IsStrobeTask(std::string_view name);
bool IsMonitorTask(std::string_view name);
Logic4Vec EvalMonitor(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalMonitorFlag(SimContext& ctx, Arena& arena, std::string_view name);
Logic4Vec EvalVcdSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                         std::string_view name);

// Shared between eval_function_args.cpp and eval_function.cpp. The subroutine
// argument-binding and body-execution helpers are defined once in
// eval_function_args.cpp; the call-dispatch entry points in eval_function.cpp
// invoke them.
struct Variable;
struct ClassObject;
void BindFunctionArgs(const ModuleItem* func, const Expr* expr, SimContext& ctx,
                      Arena& arena);

// Runs a resolved class method on a concrete object (sets `this`, binds args,
// writes back). Defined in eval_function.cpp; reused by eval_randomize.cpp to
// invoke pre_randomize()/post_randomize() on the randomized object.
Logic4Vec ExecInstanceMethodCall(ModuleItem* method, ClassObject* obj,
                                 const Expr* expr, SimContext& ctx,
                                 Arena& arena);

struct ClassTypeInfo;

// 8.10: target of a class-method invocation -- the method plus, for a
// parameterized class, its bound type so the return width resolves. Shared so
// the static-method dispatch in eval_static_method.cpp can run a method body
// without a `this`. Defined (the body) in eval_function.cpp.
struct ClassMethodTarget {
  ModuleItem* method = nullptr;
  const ClassTypeInfo* param_cls = nullptr;
};
void ExecClassMethod(ClassMethodTarget target, const Expr* expr,
                     SimContext& ctx, Arena& arena, Logic4Vec& out);

// 8.10/8.9: dispatch a static-method call that has no `this` -- either an
// unqualified call inside another static method (resolved against the enclosing
// class) or an instance-handle call `obj.static_fn()`. Both run in class scope
// so unqualified static-property access targets the single shared slot. Defined
// in eval_static_method.cpp.
bool TryEvalEnclosingStaticCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out);
bool TryEvalStaticMethodThroughInstance(ModuleItem* method, ClassObject* obj,
                                        const Expr* expr, SimContext& ctx,
                                        Arena& arena, Logic4Vec& out);

// 18.6/8.26.9: handle a built-in randomize() method call on a class handle
// (including an interface-class handle). Returns false when the call is not a
// randomize() on a resolvable class object, so normal method dispatch proceeds.
// Defined in eval_randomize.cpp.
bool TryEvalRandomizeMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out);
void WritebackOutputArgs(const ModuleItem* func, const Expr* expr,
                         SimContext& ctx, Arena& arena);
void ExecFunctionBody(const ModuleItem* func, Variable* ret_var,
                      SimContext& ctx, Arena& arena);
void WritebackQueueRefs(SimContext& ctx);
void WritebackAssocRefs(SimContext& ctx);

}  // namespace delta
