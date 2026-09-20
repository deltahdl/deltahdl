#include "simulator/eval_function_hier.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

namespace {

bool AppendHierarchicalPath(const Expr* e, std::string& path, SimContext& ctx,
                            Arena& arena);

// §23.6: a name in a path that refers to a loop generate block or to an
// instance array is followed by an instance select, a constant expression in
// brackets that selects one instance, `blk[1]` or `u[2]`; written inside a
// generate block it may be the block's own loop index, `blk[g]`, which §27.4
// makes an implicit localparam of the instance and which the running process
// reads as one. The select is rendered as the lowerer keys the instance,
// `blk[1]`, with a negative index spelled as GenBlockName spells it.
// Answers false for a part select and for an index holding an x or z bit,
// which selects no instance.
bool AppendInstanceSelect(const Expr* e, std::string& path, SimContext& ctx,
                          Arena& arena) {
  if (e->base == nullptr || e->index == nullptr || e->index_end != nullptr ||
      e->is_part_select_plus || e->is_part_select_minus) {
    return false;
  }
  if (!AppendHierarchicalPath(e->base, path, ctx, arena)) return false;
  Logic4Vec index = EvalExpr(e->index, ctx, arena);
  if (!index.IsKnown()) return false;
  path += "[" + std::to_string(SelectBoundValue(index)) + "]";
  return true;
}

// Appends the dotted path a chain of member accesses of identifiers writes,
// "u1.tk" for `u1.tk` and "x.u1.tk" for `x.u1.tk`, a name followed by an
// instance select rendered by AppendInstanceSelect, "blk[1].triple" for
// `blk[1].triple`; answering false for any other shape: a scope resolution,
// a parameterized identifier.
bool AppendHierarchicalPath(const Expr* e, std::string& path, SimContext& ctx,
                            Arena& arena) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) {
    if (!e->elements.empty()) return false;
    path += e->text;
    return true;
  }
  if (e->kind == ExprKind::kSelect) {
    return AppendInstanceSelect(e, path, ctx, arena);
  }
  if (e->kind != ExprKind::kMemberAccess || e->is_scope_resolution) {
    return false;
  }
  if (!AppendHierarchicalPath(e->lhs, path, ctx, arena)) return false;
  path += '.';
  return AppendHierarchicalPath(e->rhs, path, ctx, arena);
}

// §27.4 with §13.4: where `key` is one a generate block instance's subroutine
// was registered under, the body runs in that block's scope
// (RegisterGenBlockSubroutines in lowerer_register.cpp): the module instance
// the block is in, which the key alone cannot say -- InstanceOfKey reads
// "blk[1]." out of "blk[1].triple", and no instance is keyed so -- and the
// block's own prefixes and loop localparams. Leaves `target` alone for every
// other key.
void ApplyGenBlockScope(std::string_view key, SimContext& ctx,
                        SubroutineTarget& target) {
  const GenBlockSubroutineScope* scope = ctx.FindGenBlockSubroutineScope(key);
  if (scope == nullptr) return;
  target.gen_block = scope;
  target.inst_prefix = scope->inst_prefix;
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
  // §27.4: a generate block's subroutine found under the path as written,
  // "m.blk[1].triple" under the top's own name, already stands in its
  // instance; one below the top, "m.u1.blk[1].triple", is registered as
  // "u1.blk[1].triple" and is looked up so.
  if (target.gen_block != nullptr) return;
  target.inst_prefix = InstanceOfKey(rest);
  ApplyGenBlockScope(rest, ctx, target);
}

// The path `call` names, "tk" for a bare enable or `tk;`, "u1.tk" for a
// hierarchical one, "blk[1].triple" for one into a generate block instance;
// empty where the call names no path a module subroutine is registered
// under.
std::string CalleePath(const Expr* call, SimContext& ctx, Arena& arena) {
  if (call->kind == ExprKind::kIdentifier) return std::string(call->text);
  if (!call->callee.empty()) return std::string(call->callee);
  std::string path;
  if (!AppendHierarchicalPath(call->lhs, path, ctx, arena)) {
    return std::string();
  }
  return path;
}

// §27.4: puts the caller's generate block prefixes back in the running
// process for as long as it lives, with the callee's restored after, so an
// expression of the caller read while the process stands in the callee's
// block -- an actual, an output argument's variable -- resolves a bare name
// against the caller's own block rather than the callee's. Does nothing
// while no process runs or no call is in progress, as CallerInstancePrefix
// answers the active instance there.
class CallerGenBlockScope {
 public:
  explicit CallerGenBlockScope(SimContext& ctx) : proc_(ctx.CurrentProcess()) {
    if (proc_ == nullptr || proc_->caller_gen_prefixes.empty()) {
      proc_ = nullptr;
      return;
    }
    callee_prefixes_ = std::move(proc_->gen_prefixes);
    proc_->gen_prefixes = proc_->caller_gen_prefixes.back();
  }
  ~CallerGenBlockScope() {
    if (proc_ != nullptr) proc_->gen_prefixes = std::move(callee_prefixes_);
  }
  CallerGenBlockScope(const CallerGenBlockScope&) = delete;
  CallerGenBlockScope& operator=(const CallerGenBlockScope&) = delete;

 private:
  Process* proc_;
  std::vector<std::string> callee_prefixes_;
};

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
  std::string path = CalleePath(call, ctx, arena);
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
    ApplyGenBlockScope(relative, ctx, target);
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
  // §27.4 with §23.6: a path into a generate block instance, "blk[1].triple"
  // from the top's own processes.
  if (is_hierarchical) ApplyGenBlockScope(path, ctx, target);
  // §23.6: a path headed by a top-level module's name, from a parallel
  // hierarchy or from anywhere in the design.
  if (is_hierarchical) ResolveTopHeadedPath(path, ctx, target);
  return target;
}

void EnterCalleeInstance(SimContext& ctx, const SubroutineTarget& target) {
  Process* proc = ctx.CurrentProcess();
  if (proc == nullptr) return;
  proc->caller_inst_prefixes.push_back(std::move(proc->inst_prefix));
  proc->inst_prefix = target.inst_prefix;
  // §27.4: the block's prefixes go in beside the instance, and the caller's
  // own wait with its instance; a target of no generate block keeps the
  // caller's, as a bare call from inside a block has always run with them.
  proc->caller_gen_prefixes.push_back(proc->gen_prefixes);
  if (target.gen_block != nullptr) {
    proc->gen_prefixes = target.gen_block->gen_prefixes;
  }
}

void LeaveCalleeInstance(SimContext& ctx) {
  Process* proc = ctx.CurrentProcess();
  if (proc == nullptr || proc->caller_inst_prefixes.empty()) return;
  proc->inst_prefix = std::move(proc->caller_inst_prefixes.back());
  proc->caller_inst_prefixes.pop_back();
  if (proc->caller_gen_prefixes.empty()) return;
  proc->gen_prefixes = std::move(proc->caller_gen_prefixes.back());
  proc->caller_gen_prefixes.pop_back();
}

std::string CallerInstancePrefix(SimContext& ctx) {
  Process* proc = ctx.CurrentProcess();
  if (proc == nullptr || proc->caller_inst_prefixes.empty()) {
    return ctx.ActiveInstancePrefix();
  }
  return proc->caller_inst_prefixes.back();
}

void BindGenBlockConsts(const SubroutineTarget& target, SimContext& ctx,
                        Arena& arena) {
  if (target.gen_block == nullptr) return;
  for (const auto& [name, value] : target.gen_block->consts) {
    // §27.4: the loop index is an integer, so the localparam is 32-bit
    // signed, as Lowerer::InstallGenBlockConsts makes the block's own copy.
    Variable* var = ctx.CreateLocalVariable(name, 32, true);
    var->value = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(value));
    var->value.is_signed = true;
  }
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
  CallerGenBlockScope in_caller_block(ctx);
  BindFunctionArgs(func, expr, ctx, arena);
}

// §13.5.2: the output arguments are written back to the caller's variables,
// read in the caller's instance as the actuals were.
void WritebackInCaller(const ModuleItem* func, const Expr* expr,
                       SimContext& ctx, Arena& arena) {
  InstancePrefixOverride in_caller(ctx.InstancePrefixOverride(),
                                   CallerInstancePrefix(ctx));
  CallerGenBlockScope in_caller_block(ctx);
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
