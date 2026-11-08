#include "simulator/eval_function_hier.h"

#include <cstddef>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/process.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/unit_scopes.h"
#include "simulator/variable.h"
#include "simulator/virtual_interface.h"

namespace delta {

namespace {

bool AppendHierarchicalPath(const Expr* e, std::string& path, SimContext& ctx,
                            Arena& arena);

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

void ApplyGenBlockScope(std::string_view key, SimContext& ctx,
                        SubroutineTarget& target) {
  const GenBlockSubroutineScope* scope = ctx.FindGenBlockSubroutineScope(key);
  if (scope == nullptr) return;
  target.gen_block = scope;
  target.inst_prefix = scope->inst_prefix;
}

std::string InstanceOfKey(std::string_view key) {
  auto dot = key.rfind('.');
  return dot == std::string_view::npos ? std::string()
                                       : std::string(key.substr(0, dot + 1));
}

void ResolveTopHeadedPath(const std::string& path, SimContext& ctx,
                          SubroutineTarget& target) {
  std::string_view head = std::string_view(path).substr(0, path.find('.'));
  if (!ctx.IsTopModule(head)) return;
  std::string rest = path.substr(head.size() + 1);
  if (target.func == nullptr) target.func = ctx.FindFunction(rest);
  if (target.gen_block != nullptr) return;
  target.inst_prefix = InstanceOfKey(rest);
  ApplyGenBlockScope(rest, ctx, target);
}

bool ResolveUpwardModulePath(const std::string& path, std::string prefix,
                             SimContext& ctx, SubroutineTarget& target) {
  std::string_view head = std::string_view(path).substr(0, path.find('.'));
  for (;;) {
    auto last = prefix.size() < 2 ? std::string::npos
                                  : prefix.find_last_of('.', prefix.size() - 2);
    prefix.resize(last == std::string::npos ? 0 : last + 1);
    if (prefix.empty()) return false;
    if (ctx.FindInstanceType(
            std::string_view(prefix).substr(0, prefix.size() - 1)) == head) {
      break;
    }
  }
  std::string key = prefix + path.substr(head.size() + 1);
  target.func = ctx.FindFunction(key);
  target.inst_prefix = InstanceOfKey(key);
  ApplyGenBlockScope(key, ctx, target);
  return target.func != nullptr;
}

std::string CalleePath(const Expr* call, SimContext& ctx, Arena& arena) {
  if (call->kind == ExprKind::kIdentifier) return std::string(call->text);
  if (call->kind == ExprKind::kMemberAccess) {
    std::string path;
    if (!AppendHierarchicalPath(call, path, ctx, arena)) return std::string();
    return path;
  }
  if (!call->callee.empty()) return std::string(call->callee);
  std::string path;
  if (!AppendHierarchicalPath(call->lhs, path, ctx, arena)) {
    return std::string();
  }
  return path;
}

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

ModuleItem* ScopedOrPackageFunction(const std::string& name, SimContext& ctx) {
  if (ModuleItem* func = ctx.FindScopedFunction(name)) return func;
  return ctx.FindFunctionInPackageScope(name);
}

ModuleItem* FirstTopsOwnSubroutine(const std::string& path,
                                   const std::string& active, SimContext& ctx) {
  if (!active.empty() || path.find('.') != std::string::npos) return nullptr;
  return ctx.FindFunction(std::string(ctx.FirstTopModule()) + "." + path);
}

bool TryEnclosingDeclSubroutine(const std::string& path,
                                const std::string& active, SimContext& ctx,
                                SubroutineTarget& target) {
  if (path.find('.') != std::string::npos) return false;
  std::vector<std::string> scopes = ctx.NestedDeclOuterScopes(active);
  const ModuleItem* own =
      scopes.empty() ? nullptr : ctx.FindFunction(active + path);
  if (own != nullptr && !UnitScopes::IsUnitScope(ctx.SubroutinePackage(own)))
    return false;
  for (const std::string& scope : scopes) {
    std::string key = scope.empty()
                          ? std::string(ctx.FirstTopModule()) + "." + path
                          : scope + path;
    ModuleItem* func = ctx.FindFunction(key);
    if (func == nullptr) continue;
    target.func = func;
    target.inst_prefix = scope;
    return true;
  }
  return false;
}

ModuleItem* UnitSubroutine(const std::string& path, const std::string& active,
                           SimContext& ctx) {
  if (path.find('.') != std::string::npos) return nullptr;
  return ctx.FindFunction(UnitScopes::ScopeName(ctx.Units().UnitOf(active)) +
                          "::" + path);
}

bool IsUnitScopedCallee(const Expr* call) {
  const Expr* name = call->kind == ExprKind::kCall ? call->lhs : call;
  return name != nullptr && name->kind == ExprKind::kIdentifier &&
         name->scope_prefix == "$unit";
}

ModuleItem* UnitScopedOrFrameFunction(const Expr* call, const std::string& path,
                                      const std::string& active,
                                      SimContext& ctx) {
  ModuleItem* unit =
      IsUnitScopedCallee(call) ? UnitSubroutine(path, active, ctx) : nullptr;
  if (unit != nullptr || path.find('.') != std::string::npos) return unit;
  return ScopedOrPackageFunction(path, ctx);
}

ModuleItem* TopUnitOrBareSubroutine(const std::string& path,
                                    const std::string& active,
                                    SimContext& ctx) {
  if (ModuleItem* func = FirstTopsOwnSubroutine(path, active, ctx)) return func;
  if (ModuleItem* func = UnitSubroutine(path, active, ctx)) return func;
  return ctx.FindFunction(path);
}

const Expr* DottedCallee(const Expr* call) {
  const Expr* callee =
      call->kind == ExprKind::kCall && call->callee.empty() ? call->lhs : call;
  if (callee == nullptr || callee->kind != ExprKind::kMemberAccess ||
      callee->is_scope_resolution || callee->lhs == nullptr ||
      callee->rhs == nullptr || callee->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  return callee;
}

bool TryInterfaceInstanceCallee(const Expr* call, SimContext& ctx, Arena& arena,
                                SubroutineTarget& target) {
  const Expr* callee = DottedCallee(call);
  if (callee == nullptr) return false;
  std::string scope;
  VirtualInterfaceBase base =
      ResolveVirtualInterfaceBaseExpr(callee->lhs, ctx, arena);
  if (base.is_virtual_interface) {
    if (base.handle == kNullVirtualInterface) {
      ReportNullVirtualInterface(callee->range.start, ctx);
      return true;
    }
    scope = ctx.VirtualInterfaceScope(base.handle);
  } else if (callee->lhs->kind == ExprKind::kIdentifier) {
    scope = ctx.FindInterfacePortInstance(ctx.ActiveInstancePrefix() +
                                          std::string(callee->lhs->text));
  }
  if (scope.empty()) return false;
  std::string key = scope + "." + std::string(callee->rhs->text);
  ModuleItem* func = ctx.FindFunction(key);
  if (func == nullptr) return false;
  target.func = func;
  target.inst_prefix = scope + ".";
  ApplyGenBlockScope(key, ctx, target);
  return true;
}

bool TryPackageScopedCallee(const Expr* call, SimContext& ctx, Arena& arena,
                            SubroutineTarget& target) {
  const Expr* scoped = nullptr;
  if (call->kind == ExprKind::kCall && call->callee.empty() &&
      IsPackageScopedCall(call)) {
    scoped = call->lhs;
  } else if (call->kind == ExprKind::kMemberAccess &&
             call->is_scope_resolution) {
    if (call->lhs == nullptr || !call->lhs->elements.empty()) return true;
    scoped = call;
  } else {
    return false;
  }
  target.func = ctx.FindFunction(ScopedClassKey(scoped, arena));
  target.inst_prefix = ctx.ActiveInstancePrefix();
  return true;
}

}  // namespace

std::string EvaluatedHierarchicalPath(const Expr* e, SimContext& ctx,
                                      Arena& arena) {
  std::string path;
  if (!AppendHierarchicalPath(e, path, ctx, arena)) return std::string();
  return path;
}

bool IsPackageScopedCall(const Expr* call) {
  const Expr* scoped = call->lhs;
  if (scoped == nullptr || scoped->kind != ExprKind::kMemberAccess ||
      !scoped->is_scope_resolution) {
    return false;
  }
  return scoped->lhs != nullptr && scoped->lhs->elements.empty();
}

SubroutineTarget FindSubroutineTarget(const Expr* call, SimContext& ctx,
                                      Arena& arena) {
  SubroutineTarget target;
  if (call == nullptr) return target;
  if (TryInterfaceInstanceCallee(call, ctx, arena, target)) return target;
  if (TryPackageScopedCallee(call, ctx, arena, target)) return target;
  std::string active = ctx.ActiveInstancePrefix();
  std::string path = CalleePath(call, ctx, arena);
  if (path.empty()) return target;
  bool is_hierarchical = path.find('.') != std::string::npos;
  target.func = UnitScopedOrFrameFunction(call, path, active, ctx);
  if (target.func != nullptr) {
    target.inst_prefix = std::move(active);
    return target;
  }
  if (TryEnclosingDeclSubroutine(path, active, ctx, target)) return target;
  std::string relative = active + path;
  if (ModuleItem* func =
          active.empty() ? nullptr : ctx.FindFunction(relative)) {
    target.func = func;
    target.inst_prefix = InstanceOfKey(relative);
    ApplyGenBlockScope(relative, ctx, target);
    return target;
  }
  if (is_hierarchical && ResolveUpwardModulePath(path, active, ctx, target)) {
    return target;
  }
  target.func = TopUnitOrBareSubroutine(path, active, ctx);
  target.inst_prefix = is_hierarchical ? InstanceOfKey(path) : active;
  if (is_hierarchical) ApplyGenBlockScope(path, ctx, target);
  if (is_hierarchical) ResolveTopHeadedPath(path, ctx, target);
  return target;
}

static const Stmt* BuildForkjoinCall(const Expr* call, const ModuleItem* func,
                                     const std::vector<std::string_view>& defs,
                                     SimContext& ctx, Arena& arena) {
  auto* fork = arena.Create<Stmt>();
  fork->kind = StmtKind::kFork;
  fork->range = call->range;
  fork->join_kind = TokenKind::kKwJoin;
  if (defs.empty()) {
    ctx.GetDiag().Error(
        call->range.start,
        std::format("extern forkjoin task '{}' is defined by no module "
                    "connected to the interface",
                    func->name),
        Subclause("25.7.4"));
  }
  for (std::string_view def : defs) {
    auto* each = arena.Create<Expr>();
    each->kind = ExprKind::kCall;
    each->range = call->range;
    each->callee = def;
    if (call->kind == ExprKind::kCall) each->args = call->args;
    auto* stmt = arena.Create<Stmt>();
    stmt->kind = StmtKind::kExprStmt;
    stmt->range = call->range;
    stmt->expr = each;
    fork->fork_stmts.push_back(stmt);
  }
  return fork;
}

const Stmt* ExternForkjoinCall(const Expr* call, SimContext& ctx,
                               Arena& arena) {
  if (call == nullptr || !ctx.HasForkjoinTasks()) return nullptr;
  if (const Stmt* built = ctx.FindForkjoinCall(call)) return built;
  SubroutineTarget target = FindSubroutineTarget(call, ctx, arena);
  const ModuleItem* func = target.func;
  if (func == nullptr || !func->is_extern || !func->is_forkjoin) return nullptr;
  const std::vector<std::string_view>* defs =
      ctx.FindForkjoinTask(target.inst_prefix + std::string(func->name));
  if (defs == nullptr) return nullptr;
  const Stmt* fork = BuildForkjoinCall(call, func, *defs, ctx, arena);
  if (!defs->empty()) ctx.RecordForkjoinCall(call, fork);
  return fork;
}

static std::vector<FrameOwnerEntry>& FrameOwners(SimContext& ctx) {
  Process* proc = ctx.CurrentProcess();
  return proc != nullptr ? proc->frame_owners : ctx.ProcesslessFrameOwners();
}

void EnterStaticFrameOwner(SimContext& ctx, std::string_view owner) {
  FrameOwners(ctx).push_back({owner, 0});
}

void LeaveStaticFrameOwner(SimContext& ctx) { FrameOwners(ctx).pop_back(); }

BodyStaticFrame StaticFrameOfBody(const ModuleItem* func, SimContext& ctx,
                                  Arena& arena) {
  BodyStaticFrame frame;
  frame.name = func->name;
  std::string name(func->name);
  for (const ClassTypeInfo* level = ctx.CurrentMethodClass(); level != nullptr;
       level = level->parent) {
    auto it = level->methods.find(name);
    if (it == level->methods.end() || it->second != func) continue;
    frame.name =
        *arena.Create<std::string>(std::string(level->name) + "::" + name);
    frame.owner = level->package;
    frame.is_method = true;
    break;
  }
  return frame;
}

StaticLocalFrameScope::StaticLocalFrameScope(const ModuleItem* func,
                                             SimContext& ctx, Arena& arena)
    : ctx_(ctx) {
  BodyStaticFrame frame = StaticFrameOfBody(func, ctx, arena);
  name_ = frame.name;
  entered_ = frame.is_method;
  if (entered_) EnterStaticFrameOwner(ctx, frame.owner);
}

StaticLocalFrameScope::~StaticLocalFrameScope() {
  if (entered_) LeaveStaticFrameOwner(ctx_);
}

void EnterCalleeInstance(SimContext& ctx, const SubroutineTarget& target) {
  size_t gen_depth = target.gen_block != nullptr
                         ? target.gen_block->gen_prefixes.size()
                         : ctx.GenBlockSubroutineDepth(target.func);
  FrameOwners(ctx).push_back({target.func != nullptr
                                  ? ctx.StaticFrameOwner(target.func)
                                  : std::string_view{},
                              gen_depth});
  Process* proc = ctx.CurrentProcess();
  if (proc == nullptr) return;
  proc->caller_inst_prefixes.push_back(std::move(proc->inst_prefix));
  proc->inst_prefix = target.inst_prefix;
  proc->caller_gen_prefixes.push_back(proc->gen_prefixes);
  if (target.gen_block != nullptr) {
    proc->gen_prefixes = target.gen_block->gen_prefixes;
  }
}

void LeaveCalleeInstance(SimContext& ctx) {
  LeaveStaticFrameOwner(ctx);
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
    Variable* var = ctx.CreateLocalVariable(name, 32, true);
    var->value = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(value));
    var->value.is_signed = true;
  }
}

void BindActualsInCaller(const ModuleItem* func, const Expr* expr,
                         SimContext& ctx, Arena& arena) {
  InstancePrefixOverride in_caller(ctx.InstancePrefixOverride(),
                                   CallerInstancePrefix(ctx));
  CallerGenBlockScope in_caller_block(ctx);
  BindFunctionArgs(func, expr, ctx, arena);
}

void WritebackInCaller(const ModuleItem* func, const Expr* expr,
                       SimContext& ctx, Arena& arena) {
  InstancePrefixOverride in_caller(ctx.InstancePrefixOverride(),
                                   CallerInstancePrefix(ctx));
  CallerGenBlockScope in_caller_block(ctx);
  WritebackOutputArgs(func, expr, ctx, arena);
  WritebackQueueRefs(ctx);
  WritebackAssocRefs(ctx);
}

void ExecFunctionBodyInCallee(const SubroutineTarget& target, const Expr* call,
                              Variable* ret_var, SimContext& ctx,
                              Arena& arena) {
  InstancePrefixOverride in_callee(ctx.InstancePrefixOverride(),
                                   target.inst_prefix);
  ExecFunctionBody(target.func, call, ret_var, ctx, arena);
}

}  // namespace delta

namespace delta {
namespace {

const Stmt* FindStaticLocalDecl(const std::vector<Stmt*>& stmts,
                                std::string_view name, bool every_static);

const Stmt* FindStaticLocalDeclIn(const Stmt* s, std::string_view name,
                                  bool every_static) {
  if (s == nullptr) return nullptr;
  if (s->kind == StmtKind::kVarDecl) {
    bool is_static = s->var_is_static ||
                     (every_static && !s->var_is_automatic && !s->var_is_param);
    return is_static && s->var_name == name ? s : nullptr;
  }
  if (const Stmt* found = FindStaticLocalDecl(s->stmts, name, every_static)) {
    return found;
  }
  if (const Stmt* found = FindStaticLocalDeclIn(s->body, name, every_static)) {
    return found;
  }
  if (const Stmt* found =
          FindStaticLocalDeclIn(s->then_branch, name, every_static)) {
    return found;
  }
  return FindStaticLocalDeclIn(s->else_branch, name, every_static);
}

const Stmt* FindStaticLocalDecl(const std::vector<Stmt*>& stmts,
                                std::string_view name, bool every_static) {
  for (const Stmt* s : stmts) {
    if (const Stmt* found = FindStaticLocalDeclIn(s, name, every_static)) {
      return found;
    }
  }
  return nullptr;
}

}  // namespace

Variable* FunctionStaticLocal(const Expr* member, SimContext& ctx,
                              Arena& arena) {
  if (member == nullptr || member->kind != ExprKind::kMemberAccess ||
      member->lhs == nullptr || member->rhs == nullptr ||
      member->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  Expr call;
  call.kind = ExprKind::kCall;
  call.lhs = member->lhs;
  SubroutineTarget target = FindSubroutineTarget(&call, ctx, arena);
  if (target.func == nullptr ||
      target.func->kind != ModuleItemKind::kFunctionDecl) {
    return nullptr;
  }
  std::string_view var = member->rhs->text;
  bool is_static_sub = !target.func->is_automatic;
  const Stmt* decl =
      FindStaticLocalDecl(target.func->func_body_stmts, var, is_static_sub);
  if (decl == nullptr) return nullptr;
  EnterCalleeInstance(ctx, target);
  Variable* found = ctx.FindStaticFuncVar(target.func->name, var);
  if (found == nullptr) {
    ctx.PushStaticScope(target.func->name);
    ExecFuncVarDecl(decl, {target.func->name, is_static_sub}, ctx, arena);
    ctx.PopStaticScope(target.func->name);
    found = ctx.FindStaticFuncVar(target.func->name, var);
  }
  LeaveCalleeInstance(ctx);
  return found;
}

}  // namespace delta
