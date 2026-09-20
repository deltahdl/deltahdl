#include "simulator/eval_function_hier.h"

#include <string>
#include <string_view>
#include <utility>

#include "parser/ast_expr.h"
#include "simulator/eval_function_internal.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

// Appends the dotted path a chain of member accesses of identifiers writes,
// "u1.tk" for `u1.tk` and "x.u1.tk" for `x.u1.tk`, answering false for any
// other shape: a select in the chain (an instance array element, §23.6's
// instance select, is not resolved here), a scope resolution, a
// parameterized identifier.
bool AppendHierarchicalPath(const Expr* e, std::string& path) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) {
    if (!e->elements.empty()) return false;
    path += e->text;
    return true;
  }
  if (e->kind != ExprKind::kMemberAccess || e->is_scope_resolution) {
    return false;
  }
  if (!AppendHierarchicalPath(e->lhs, path)) return false;
  path += '.';
  return AppendHierarchicalPath(e->rhs, path);
}

// The instance a registered key names: the key up to and including its last
// `.`, "u1." for "u1.tk", and empty for a bare name, the top's.
std::string InstanceOfKey(std::string_view key) {
  auto dot = key.rfind('.');
  return dot == std::string_view::npos ? std::string()
                                       : std::string(key.substr(0, dot + 1));
}

// §26.3: a subroutine called through the package scope resolution operator,
// `pk::f(x)`, parses as a call with no callee text and the scoped name as its
// base; the lowerer registers every package subroutine under that "pk::f"
// key (RegisterPackageScopedSubroutines), so the lookup goes by it. A class
// scope never reaches this key: TryEvalClassScopeCall and the instance-task
// path take those calls before the registry is asked.
bool IsPackageScopedCall(const Expr* call) {
  const Expr* scoped = call->lhs;
  if (scoped == nullptr || scoped->kind != ExprKind::kMemberAccess ||
      !scoped->is_scope_resolution) {
    return false;
  }
  return scoped->lhs != nullptr && scoped->lhs->elements.empty();
}

// §23.6: the complete path name to any object starts at a top-level module
// and may be used from any level of the hierarchy or from a parallel one, so
// "m.t1" written in the other top-level module n is m's t1, and "m.u1.tk" the
// tk of m's child u1. A top's declarations are keyed under no prefix, as
// Process::inst_prefix is empty there, so the instance the body runs in is
// the path after the top's name: none for "m.t1", "u1." for "m.u1.tk". The
// top's own subroutines are registered under its name too (LowerModule), so
// "m.t1" as written answers m's t1 ahead of the bare "t1" of whichever top
// registered last; a subroutine of an instance below the top is keyed with
// the top's name left off. Leaves `target` alone when the head names no top.
void ResolveTopHeadedPath(const std::string& path, SimContext& ctx,
                          SubroutineTarget& target) {
  std::string_view head = std::string_view(path).substr(0, path.find('.'));
  if (!ctx.IsTopModule(head)) return;
  std::string rest = path.substr(head.size() + 1);
  if (target.func == nullptr) target.func = ctx.FindFunction(rest);
  target.inst_prefix = InstanceOfKey(rest);
}

// The path `call` names, "tk" for a bare enable or `tk;`, "u1.tk" for a
// hierarchical one; empty where the call names no path a module subroutine
// is registered under.
std::string CalleePath(const Expr* call) {
  if (call->kind == ExprKind::kIdentifier) return std::string(call->text);
  if (!call->callee.empty()) return std::string(call->callee);
  std::string path;
  if (!AppendHierarchicalPath(call->lhs, path)) return std::string();
  return path;
}

}  // namespace

SubroutineTarget FindSubroutineTarget(const Expr* call, SimContext& ctx,
                                      Arena& arena) {
  SubroutineTarget target;
  if (call == nullptr) return target;
  std::string active = ctx.ActiveInstancePrefix();
  if (call->kind == ExprKind::kCall && call->callee.empty() &&
      IsPackageScopedCall(call)) {
    target.func = ctx.FindFunction(ScopedClassKey(call->lhs, arena));
    target.inst_prefix = std::move(active);
    return target;
  }
  std::string path = CalleePath(call);
  if (path.empty()) return target;
  // §23.6: the first node of a path may be the top of the hierarchy the path
  // is used from, so "u1.tk" written in instance "x." is "x.u1.tk" first,
  // and the lowerer registers each instance's subroutines under that
  // prefixed key (RegisterInstanceSubroutines). The same lookup makes a bare
  // name the calling instance's own declaration ahead of another module's
  // registered under the same bare name. With no prefix in force the
  // relative key is the path itself, answered below with a top's name at its
  // head read as §23.6's root rather than as an instance.
  std::string relative = active + path;
  if (ModuleItem* func =
          active.empty() ? nullptr : ctx.FindFunction(relative)) {
    target.func = func;
    target.inst_prefix = InstanceOfKey(relative);
    return target;
  }
  // A path from the top of the design, "u1.tk" as written; a bare name found
  // here is the top's, a package's or the compilation unit's and runs where
  // the caller stands, as it did before instances were registered by prefix.
  target.func = ctx.FindFunction(path);
  bool is_hierarchical = path.find('.') != std::string::npos;
  // §26.2: a bare callee inside a package's frame -- a package variable's
  // initializer or a package subroutine's body calling another of the
  // package's, or one its import brings in -- is registered under the
  // package's "pkg::name" key and under no bare one unless imported.
  if (target.func == nullptr && !is_hierarchical)
    target.func = ctx.FindFunctionInPackageScope(path);
  target.inst_prefix = is_hierarchical ? InstanceOfKey(path) : active;
  // §23.6: a path headed by a top-level module's name, from a parallel
  // hierarchy or from anywhere in the design.
  if (is_hierarchical) ResolveTopHeadedPath(path, ctx, target);
  return target;
}

void EnterCalleeInstance(SimContext& ctx, std::string_view inst_prefix) {
  Process* proc = ctx.CurrentProcess();
  if (proc == nullptr) return;
  proc->caller_inst_prefixes.push_back(std::move(proc->inst_prefix));
  proc->inst_prefix = std::string(inst_prefix);
}

void LeaveCalleeInstance(SimContext& ctx) {
  Process* proc = ctx.CurrentProcess();
  if (proc == nullptr || proc->caller_inst_prefixes.empty()) return;
  proc->inst_prefix = std::move(proc->caller_inst_prefixes.back());
  proc->caller_inst_prefixes.pop_back();
}

std::string CallerInstancePrefix(SimContext& ctx) {
  Process* proc = ctx.CurrentProcess();
  if (proc == nullptr || proc->caller_inst_prefixes.empty()) {
    return ctx.ActiveInstancePrefix();
  }
  return proc->caller_inst_prefixes.back();
}

// §13.5: the actuals are expressions of the caller, so they are read in the
// instance the call was written in, while the process itself stands in the
// callee's (EnterCalleeInstance) so that a static subroutine's formals join
// that instance's frame (§13.3.2). The binding never suspends, so the
// override that names the caller's instance for it is scoped over it alone.
void BindActualsInCaller(const ModuleItem* func, const Expr* expr,
                         SimContext& ctx, Arena& arena) {
  InstancePrefixOverride in_caller(ctx.InstancePrefixOverride(),
                                   CallerInstancePrefix(ctx));
  BindFunctionArgs(func, expr, ctx, arena);
}

// §13.5.2: the output arguments are written back to the caller's variables,
// read in the caller's instance as the actuals were.
void WritebackInCaller(const ModuleItem* func, const Expr* expr,
                       SimContext& ctx, Arena& arena) {
  InstancePrefixOverride in_caller(ctx.InstancePrefixOverride(),
                                   CallerInstancePrefix(ctx));
  WritebackOutputArgs(func, expr, ctx, arena);
  WritebackQueueRefs(ctx);
  WritebackAssocRefs(ctx);
}

// §13.4 with §23.6: a function's body runs in the callee's instance. The
// process already stands there, and the override naming it is for a call
// made while the actuals of an enclosing call are being read, `u1.tk(u2.f(1))`,
// where the caller's instance is in force through BindActualsInCaller. A
// function never suspends, so the override is scoped over the body.
void ExecFunctionBodyInCallee(const ModuleItem* func,
                              std::string_view inst_prefix, Variable* ret_var,
                              SimContext& ctx, Arena& arena) {
  InstancePrefixOverride in_callee(ctx.InstancePrefixOverride(), inst_prefix);
  ExecFunctionBody(func, ret_var, ctx, arena);
}

}  // namespace delta
