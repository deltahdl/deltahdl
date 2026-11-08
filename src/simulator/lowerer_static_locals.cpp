#include <algorithm>
#include <cstddef>
#include <string_view>
#include <tuple>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/declared_class_key.h"
#include "simulator/deferred_caller.h"
#include "simulator/eval_function_hier.h"
#include "simulator/eval_function_internal.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/static_aggregate.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/vcd_dump_state.h"
#include "simulator/vcd_writer.h"

namespace delta {

namespace {

void CollectStaticInits(const Stmt* s, std::vector<const Stmt*>& out) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) {
    if (s->var_is_static && s->var_init != nullptr) out.push_back(s);
    return;
  }
  for (const Stmt* sub : s->stmts) CollectStaticInits(sub, out);
  for (const Stmt* sub : s->fork_stmts) CollectStaticInits(sub, out);
  CollectStaticInits(s->then_branch, out);
  CollectStaticInits(s->else_branch, out);
  CollectStaticInits(s->body, out);
  CollectStaticInits(s->for_body, out);
  for (const CaseItem& item : s->case_items) CollectStaticInits(item.body, out);
}

std::vector<const Stmt*> StaticInitsOf(const ModuleItem* func) {
  std::vector<const Stmt*> out;
  for (const Stmt* s : func->func_body_stmts) CollectStaticInits(s, out);
  return out;
}

std::vector<const Stmt*> StaticInitsOf(const Stmt* body) {
  std::vector<const Stmt*> out;
  CollectStaticInits(body, out);
  return out;
}

StaticFrame StaticLocalsFrame(std::string_view name, const ModuleItem* func) {
  return {name, func->is_static && !func->is_automatic};
}

void BindOwnerGenBlockConsts(const RtlirGenBlockSubroutine* gen_block,
                             SimContext& ctx, Arena& arena) {
  if (gen_block == nullptr) return;
  GenBlockSubroutineScope scope;
  scope.consts = gen_block->gen_block_consts;
  SubroutineTarget target;
  target.gen_block = &scope;
  BindGenBlockConsts(target, ctx, arena);
}

void InitSubroutineStatics(const StaticLocalOwner& owner, SimContext& ctx,
                           Arena& arena) {
  const ModuleItem* func = owner.subroutine;
  ctx.PushStaticScope(func->name);
  ctx.EnterSubroutinePackage(func);
  BindOwnerGenBlockConsts(owner.gen_block, ctx, arena);
  for (const Stmt* decl : StaticInitsOf(func)) {
    ExecFuncVarDecl(decl, StaticLocalsFrame(func->name, func), ctx, arena);
  }
  ctx.PopStaticScope(func->name);
}

void InitOwnedSubroutineStatics(SimContext& ctx, Arena& arena) {
  for (const ModuleItem* func : ctx.OwnedSubroutines()) {
    if (StaticInitsOf(func).empty()) continue;
    Process stand_in;
    stand_in.stand_in = true;
    stand_in.is_static_init = true;
    stand_in.frame_owners.push_back({ctx.StaticFrameOwner(func), 0});
    CallerStandIn in_owner(&stand_in, ctx);
    StaticLocalOwner owner;
    owner.subroutine = func;
    InitSubroutineStatics(owner, ctx, arena);
  }
}

void InitClassMethodStatics(const ClassTypeInfo* cls, SimContext& ctx,
                            Arena& arena) {
  for (const auto& [name, func] : cls->methods) {
    std::vector<const Stmt*> inits = StaticInitsOf(func);
    if (inits.empty()) continue;
    ctx.PushMethodClass(cls);
    ctx.PushScope();
    ctx.EnterSubroutinePackage(func);
    {
      StaticLocalFrameScope frame(func, ctx, arena);
      for (const Stmt* decl : inits)
        ExecFuncVarDecl(decl, StaticLocalsFrame(frame.Name(), func), ctx,
                        arena);
    }
    ctx.PopScope();
    ctx.PopMethodClass();
  }
}

void InitPackageClassMethodStatics(SimContext& ctx, Arena& arena) {
  for (const ClassTypeInfo* cls : ctx.RegisteredClassTypes(true)) {
    if (cls->decl == nullptr || cls->package.empty()) continue;
    Process stand_in;
    stand_in.stand_in = true;
    stand_in.is_static_init = true;
    CallerStandIn in_owner(&stand_in, ctx);
    InitClassMethodStatics(cls, ctx, arena);
  }
}

const ClassTypeInfo* OutermostClass(const ClassTypeInfo* cls) {
  while (cls->enclosing != nullptr) cls = cls->enclosing;
  return cls;
}

std::string_view InstanceClassScope(const ClassDecl* decl,
                                    std::string_view prefix,
                                    const std::vector<ClassTypeInfo*>& held) {
  bool own = std::ranges::any_of(held, [&](const ClassTypeInfo* cls) {
    return cls->instance_scope == prefix && cls->decl == decl;
  });
  return own ? prefix : std::string_view{};
}

std::vector<const ClassTypeInfo*> InstanceClasses(
    const std::vector<ClassDecl*>& decls, std::string_view prefix,
    const SimContext& ctx) {
  std::vector<ClassTypeInfo*> held = ctx.RegisteredClassTypes(true);
  std::vector<const ClassTypeInfo*> out;
  for (const ClassDecl* decl : decls) {
    std::string_view scope = InstanceClassScope(decl, prefix, held);
    for (const ClassTypeInfo* cls : held) {
      if (cls->package.empty() && cls->instance_scope == scope &&
          OutermostClass(cls)->decl == decl) {
        out.push_back(cls);
      }
    }
  }
  return out;
}

void InitModuleClassMethodStatics(const std::vector<ClassDecl*>& decls,
                                  std::string_view prefix, SimContext& ctx,
                                  Arena& arena) {
  for (const ClassTypeInfo* cls : InstanceClasses(decls, prefix, ctx))
    InitClassMethodStatics(cls, ctx, arena);
}

void StandInFor(const StaticLocalOwner& owner, Process& stand_in) {
  stand_in.stand_in = true;
  stand_in.is_static_init = true;
  stand_in.inst_prefix = owner.inst_prefix;
  if (owner.gen_block != nullptr) {
    stand_in.gen_prefixes.assign(owner.gen_block->gen_block_prefixes.begin(),
                                 owner.gen_block->gen_block_prefixes.end());
  }
  if (owner.process != nullptr) {
    stand_in.gen_prefixes = owner.process->gen_prefixes;
    stand_in.gen_block_name = owner.process->gen_block_name;
    stand_in.saved_scope_stack = owner.process->saved_scope_stack;
  }
}

void MakeExprSpecializations(const Expr* e, SimContext& ctx, Arena& arena) {
  if (e == nullptr) return;
  if (e->has_param_spec && !e->elements.empty())
    ScopeNamedSpecialization(e, ctx, arena);
  ForEachExprChild(e, [&](const Expr* child) {
    MakeExprSpecializations(child, ctx, arena);
  });
}

void MakeStmtSpecializations(const Stmt* s, SimContext& ctx, Arena& arena) {
  if (s == nullptr) return;
  const DataType& type = s->var_decl_type;
  if (s->kind == StmtKind::kVarDecl && !type.type_params.empty()) {
    SpecializationOf(ctx.FindClassType(DeclaredClassKey(type, ctx, arena)),
                     type.type_params, ctx, arena);
  }
  ForEachChildExpr(
      s, [&](const Expr* e) { MakeExprSpecializations(e, ctx, arena); });
  ForEachChildStmt(
      s, [&](const Stmt* sub) { MakeStmtSpecializations(sub, ctx, arena); });
}

void MakeSubroutineSpecializations(const ModuleItem* func,
                                   const RtlirGenBlockSubroutine* gen_block,
                                   SimContext& ctx, Arena& arena) {
  ctx.PushScope();
  ctx.EnterSubroutinePackage(func);
  BindOwnerGenBlockConsts(gen_block, ctx, arena);
  for (const Stmt* s : func->func_body_stmts)
    MakeStmtSpecializations(s, ctx, arena);
  ctx.PopScope();
}

bool IsUnspecializedGeneric(const ClassTypeInfo* cls) {
  return !cls->decl->params.empty() && cls->param_actuals == nullptr;
}

std::vector<const ClassTypeInfo*> PackageClasses(const SimContext& ctx) {
  std::vector<const ClassTypeInfo*> out;
  for (const ClassTypeInfo* cls : ctx.RegisteredClassTypes(true)) {
    if (!cls->package.empty()) out.push_back(cls);
  }
  return out;
}

bool WalkMethodSpecializations(const std::vector<const ClassTypeInfo*>& classes,
                               std::unordered_set<const ClassTypeInfo*>& walked,
                               SimContext& ctx, Arena& arena) {
  bool grew = false;
  for (const ClassTypeInfo* cls : classes) {
    if (IsUnspecializedGeneric(cls) || !walked.insert(cls).second) continue;
    grew = true;
    ctx.PushMethodClass(cls);
    for (const auto& [name, func] : cls->methods)
      MakeSubroutineSpecializations(func, nullptr, ctx, arena);
    ctx.PopMethodClass();
  }
  return grew;
}

void MakeMethodSpecializations(const std::vector<StaticLocalOwner>& owners,
                               SimContext& ctx, Arena& arena) {
  std::vector<std::unordered_set<const ClassTypeInfo*>> walked(owners.size() +
                                                               1);
  for (bool grew = true; grew;) {
    grew = false;
    for (std::size_t i = 0; i < owners.size(); ++i) {
      if (owners[i].classes == nullptr) continue;
      Process stand_in;
      StandInFor(owners[i], stand_in);
      CallerStandIn in_owner(&stand_in, ctx);
      if (WalkMethodSpecializations(
              InstanceClasses(*owners[i].classes, owners[i].inst_prefix, ctx),
              walked[i], ctx, arena)) {
        grew = true;
      }
    }
    Process stand_in;
    StandInFor(StaticLocalOwner{}, stand_in);
    CallerStandIn in_no_instance(&stand_in, ctx);
    if (WalkMethodSpecializations(PackageClasses(ctx), walked.back(), ctx,
                                  arena)) {
      grew = true;
    }
  }
}

bool IsBlockStaticDecl(const Stmt* s) {
  return s != nullptr && s->kind == StmtKind::kVarDecl && !s->var_is_automatic;
}

void MakeNamedBlockStatics(const Stmt* s, SimContext& ctx, Arena& arena) {
  if (s == nullptr || s->kind == StmtKind::kRandsequence) return;
  bool named = !s->label.empty() &&
               (s->kind == StmtKind::kBlock || s->kind == StmtKind::kFork);
  if (named) {
    ctx.PushStaticScope(ctx.StmtFrameName(s));
    ctx.PushActiveNamedScope(s->label);
    if (s->kind == StmtKind::kFork)
      ctx.Vcd().SetVcdScopeKind(ActiveNamedScopePath(ctx), VcdScopeKind::kFork);
  }
  ForEachChildStmt(s, [&](const Stmt* sub) {
    if (named && IsBlockStaticDecl(sub)) {
      ExecVarDeclImpl(sub, ctx, arena);
    } else {
      MakeNamedBlockStatics(sub, ctx, arena);
    }
  });
  if (named) {
    ctx.PopActiveNamedScope();
    RetainBlockAggregates(*s, ctx.StmtFrameName(s), ctx, arena);
    ctx.PopStaticScope(ctx.StmtFrameName(s));
  }
}

}  // namespace

const RtlirGenBlockSubroutine* DeclaringGenBlock(const ModuleItem* func,
                                                 const RtlirModule* mod) {
  auto it = std::ranges::find_if(
      mod->gen_block_subroutines, [&](const RtlirGenBlockSubroutine& sub) {
        const SourceLoc& at = sub.decl->loc;
        return std::tie(sub.decl->name, at.file_id, at.line, at.column) ==
               std::tie(func->name, func->loc.file_id, func->loc.line,
                        func->loc.column);
      });
  return it != mod->gen_block_subroutines.end() ? &*it : nullptr;
}

void Lowerer::RecordStaticLocalSubroutines(const RtlirModule* mod) {
  if (!mod->class_decls.empty()) {
    static_local_owners_.push_back(
        {.inst_prefix = inst_prefix_, .classes = &mod->class_decls});
  }
  for (const ModuleItem* func : mod->function_decls) {
    if (!func->method_class.empty()) continue;
    if (const RtlirGenBlockSubroutine* sub = DeclaringGenBlock(func, mod)) {
      ctx_.RegisterGenBlockSubroutineDepth(func,
                                           sub->gen_block_prefixes.size());
      continue;
    }
    StaticLocalOwner owner{.inst_prefix = inst_prefix_, .subroutine = func};
    specializing_code_.push_back(owner);
    if (!StaticInitsOf(func).empty()) static_local_owners_.push_back(owner);
  }
  for (const RtlirGenBlockSubroutine& sub : mod->gen_block_subroutines) {
    ctx_.RegisterGenBlockSubroutineDepth(sub.decl,
                                         sub.gen_block_prefixes.size());
    StaticLocalOwner owner{
        .inst_prefix = inst_prefix_, .subroutine = sub.decl, .gen_block = &sub};
    specializing_code_.push_back(owner);
    if (!StaticInitsOf(sub.decl).empty()) static_local_owners_.push_back(owner);
  }
}

void Lowerer::RecordStaticLocalProcess(const Process* p, const Stmt* body) {
  StaticLocalOwner owner{
      .inst_prefix = inst_prefix_, .process = p, .body = body};
  specializing_code_.push_back(owner);
  if (!StaticInitsOf(body).empty()) static_local_owners_.push_back(owner);
}

void Lowerer::MakeNamedSpecializations() {
  for (const StaticLocalOwner& owner : specializing_code_) {
    Process stand_in;
    StandInFor(owner, stand_in);
    CallerStandIn in_owner(&stand_in, ctx_);
    if (owner.subroutine != nullptr) {
      MakeSubroutineSpecializations(owner.subroutine, owner.gen_block, ctx_,
                                    arena_);
      continue;
    }
    ctx_.PushScope();
    MakeStmtSpecializations(owner.body, ctx_, arena_);
    ctx_.PopScope();
  }
  {
    Process stand_in;
    StandInFor(StaticLocalOwner{}, stand_in);
    CallerStandIn in_no_instance(&stand_in, ctx_);
    for (const ModuleItem* func : ctx_.OwnedSubroutines())
      MakeSubroutineSpecializations(func, nullptr, ctx_, arena_);
  }
  MakeMethodSpecializations(static_local_owners_, ctx_, arena_);
}

void Lowerer::InitializeStaticLocals() {
  InitOwnedSubroutineStatics(ctx_, arena_);
  InitPackageClassMethodStatics(ctx_, arena_);
  for (const StaticLocalOwner& owner : static_local_owners_) {
    Process stand_in;
    StandInFor(owner, stand_in);
    CallerStandIn in_owner(&stand_in, ctx_);
    if (owner.classes != nullptr) {
      InitModuleClassMethodStatics(*owner.classes, owner.inst_prefix, ctx_,
                                   arena_);
      continue;
    }
    if (owner.subroutine != nullptr) {
      InitSubroutineStatics(owner, ctx_, arena_);
      continue;
    }
    ctx_.PushScope();
    for (const Stmt* decl : StaticInitsOf(owner.body))
      ExecVarDeclImpl(decl, ctx_, arena_);
    ctx_.PopScope();
  }
  for (const StaticLocalOwner& owner : specializing_code_) {
    if (owner.body == nullptr) continue;
    Process stand_in;
    StandInFor(owner, stand_in);
    CallerStandIn in_owner(&stand_in, ctx_);
    ctx_.PushScope();
    MakeNamedBlockStatics(owner.body, ctx_, arena_);
    ctx_.PopScope();
  }
}

}  // namespace delta
