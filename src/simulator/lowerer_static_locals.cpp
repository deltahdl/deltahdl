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
#include "simulator/stmt_exec_internal.h"
#include "simulator/vcd_dump_state.h"
#include "simulator/vcd_writer.h"

namespace delta {

namespace {

// §6.21: the `static` local declarations of `s` that give an initial value,
// in the order the source writes them, at whatever depth of block, branch,
// loop, fork or case item. §6.21 has every other local of a static scope that
// gives one say `automatic` (ReportImplicitlyStaticInit in the elaborator),
// so these are all the static locals an initializer sets.
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

// The frame ExecFuncVarDecl makes the static locals of `func` in, held under
// `name`.
StaticFrame StaticLocalsFrame(std::string_view name, const ModuleItem* func) {
  return {name, func->is_static && !func->is_automatic};
}

// §27.4: the loop constants of `gen_block`, the generate block instance
// declaring the subroutine whose frame is innermost, bound in that frame as a
// call binds them (BindGenBlockConsts); nothing for a subroutine no generate
// block declares.
void BindOwnerGenBlockConsts(const RtlirGenBlockSubroutine* gen_block,
                             SimContext& ctx, Arena& arena) {
  if (gen_block == nullptr) return;
  GenBlockSubroutineScope scope;
  scope.consts = gen_block->gen_block_consts;
  SubroutineTarget target;
  target.gen_block = &scope;
  BindGenBlockConsts(target, ctx, arena);
}

// §13.4.2: the static locals of `owner`'s subroutine, made in its static frame
// as a call makes them (EvalFunctionCall): the frame entered with the
// subroutine's package, and a generate block instance's subroutine with the
// block's loop constants beside them.
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

// §27.4: whether `func` is one of the subroutines a generate block of `mod`
// declares. The elaborator lists such a subroutine among the module's own
// function_decls as well, under its bare name and possibly as a copy, so it is
// told by where it is written; made from there, its static locals were made
// without the block's loop constants their initializers read.
bool IsGenBlockSubroutine(const ModuleItem* func, const RtlirModule* mod) {
  return std::ranges::any_of(
      mod->gen_block_subroutines, [&](const RtlirGenBlockSubroutine& sub) {
        const SourceLoc& at = sub.decl->loc;
        return std::tie(sub.decl->name, at.file_id, at.line, at.column) ==
               std::tie(func->name, func->loc.file_id, func->loc.line,
                        func->loc.column);
      });
}

// §10.5 with §13.4.2: the static locals of the package and compilation-unit
// subroutines, each made in the one frame its calls share, kept under its
// package's or unit's name (DeclaredNameTables::StaticFrameOwner) whatever
// instance calls it, so standing in no instance.
void InitOwnedSubroutineStatics(SimContext& ctx, Arena& arena) {
  for (const ModuleItem* func : ctx.OwnedSubroutines()) {
    if (StaticInitsOf(func).empty()) continue;
    Process stand_in;
    stand_in.stand_in = true;
    stand_in.is_static_init = true;
    stand_in.frame_owners.push_back(ctx.StaticFrameOwner(func));
    CallerStandIn in_owner(&stand_in, ctx);
    StaticLocalOwner owner;
    owner.subroutine = func;
    InitSubroutineStatics(owner, ctx, arena);
  }
}

// §10.5 with §8.6 and §6.21: the static locals of the methods `cls` declares,
// each made in the frame a call keeps them in, the one StaticFrameOfBody names
// after the class, kept under the class's package or unit, or, for a module's
// class, under the instance the caller stands in. The class is running and
// the frame carries the method's package, as ExecClassMethod has them, so an
// initializer reads the specialization's parameters and the package's names
// as the call's own declaration would.
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

// §10.5 with §8.6: the method static locals of every class a package or the
// compilation unit holds, the specializations of one made by now among them
// (§8.25), each class's in the frames its calls share under that package or
// unit, so standing in no instance.
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

// §8.25: the scope the classes of `decl` held for the instance `prefix` stand
// under: the instance's own, where it was given copies of its own
// (Lowerer::RegisterChildClasses), and otherwise none, the classes being
// shared.
std::string_view InstanceClassScope(const ClassDecl* decl,
                                    std::string_view prefix,
                                    const std::vector<ClassTypeInfo*>& held) {
  bool own = std::ranges::any_of(held, [&](const ClassTypeInfo* cls) {
    return cls->instance_scope == prefix && cls->decl == decl;
  });
  return own ? prefix : std::string_view{};
}

// The classes the instance `prefix` holds of the classes `decls` its module
// declares (InstanceClassScope), with each class nested in one (§8.23) and
// each specialization of one made by now (§8.25).
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

// §10.5 with §8.6: the method static locals of the classes the instance
// `prefix` holds of those `decls` its module declares, made standing in that
// instance, whose frames a call keeps under it (SimContext::StaticFrameKey).
void InitModuleClassMethodStatics(const std::vector<ClassDecl*>& decls,
                                  std::string_view prefix, SimContext& ctx,
                                  Arena& arena) {
  for (const ClassTypeInfo* cls : InstanceClasses(decls, prefix, ctx))
    InitClassMethodStatics(cls, ctx, arena);
}

// The process `owner`'s code runs standing in before any procedure starts:
// the instance and the generate block it was lowered in, and for a procedure,
// the scopes its own process carries.
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

// §8.25: the specializations of parameterized classes `e` and the
// expressions within it name through a class scope prefix, `C#(3)::s` or
// `C#(3)::f()`, each made as the evaluation of the prefix makes it
// (ScopeNamedSpecialization), with its actuals read in the running scope.
void MakeExprSpecializations(const Expr* e, SimContext& ctx, Arena& arena) {
  if (e == nullptr) return;
  if (e->has_param_spec && !e->elements.empty())
    ScopeNamedSpecialization(e, ctx, arena);
  ForEachExprChild(e, [&](const Expr* child) {
    MakeExprSpecializations(child, ctx, arena);
  });
}

// §8.25: those `s` and the statements within it name, through their
// expressions and through a local declaration of a specialization's type,
// `C#(8) h;`, made as the declaration makes it (RecordClassParamActuals).
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

// §8.25: those the body of `func` names, read in a frame of its own carrying
// its package and, for a generate block instance's subroutine, the block's
// loop constants, as a call's frame carries them.
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

// §8.25: a parameterized class's declaration, which is no specialization the
// design names until a `#(...)` list or the bare name does; its methods' code
// is the specializations' and is read under each of them. The classes read
// are all declared (InstanceClasses, PackageClasses); a built-in class is
// neither a package's nor an instance's.
bool IsUnspecializedGeneric(const ClassTypeInfo* cls) {
  return !cls->decl->params.empty() && cls->param_actuals == nullptr;
}

// The classes a package or the compilation unit holds, whose methods' code
// runs under that package or unit whatever instance calls it.
std::vector<const ClassTypeInfo*> PackageClasses(const SimContext& ctx) {
  std::vector<const ClassTypeInfo*> out;
  for (const ClassTypeInfo* cls : ctx.RegisteredClassTypes(true)) {
    if (!cls->package.empty()) out.push_back(cls);
  }
  return out;
}

// §8.25: those the methods of `classes` name that are not in `walked`, each
// read with its class running so that an actual naming one of the class's own
// parameters, `C#(K)::s` in a method of `E#(30)`, reads that
// specialization's; whether any class was read.
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

// §8.25 with §23.9: those the methods of every class name, a module's class's
// read standing in each instance `owners` records as holding one, so that an
// actual naming a parameter of the module, `C#(P)::s`, reads the value that
// instance gives it, and a package's or the unit's class's standing in none.
// A specialization made here has methods of its own to read, so the classes
// are gone over again until a pass makes none.
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

// A static declaration of a variable, which every declaration in a
// procedure's block is unless written `automatic` (§6.21).
bool IsBlockStaticDecl(const Stmt* s) {
  return s != nullptr && s->kind == StmtKind::kVarDecl && !s->var_is_automatic;
}

// §6.21 with §23.6: the static variables of the named begin-end and fork
// blocks of `s`, each made in the frame its block keeps between activations
// (StmtFrameName) with the block's named scopes entered, so that the
// declaration binds it under its hierarchical name (BindNamedBlockVariable)
// and, when the block runs, finds it there and stands in it. A randsequence's
// code blocks are automatic scopes (§18.17) and keep none.
void MakeNamedBlockStatics(const Stmt* s, SimContext& ctx, Arena& arena) {
  if (s == nullptr || s->kind == StmtKind::kRandsequence) return;
  bool named = !s->label.empty() &&
               (s->kind == StmtKind::kBlock || s->kind == StmtKind::kFork);
  if (named) {
    ctx.PushStaticScope(ctx.StmtFrameName(s));
    ctx.PushActiveNamedScope(s->label);
    // §21.7.2.3: a dump opens a named parallel block's scope as a fork.
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
    ctx.PopStaticScope(ctx.StmtFrameName(s));
  }
}

}  // namespace

void Lowerer::RecordStaticLocalSubroutines(const RtlirModule* mod) {
  if (!mod->class_decls.empty()) {
    static_local_owners_.push_back(
        {.inst_prefix = inst_prefix_, .classes = &mod->class_decls});
  }
  for (const ModuleItem* func : mod->function_decls) {
    if (!func->method_class.empty() || IsGenBlockSubroutine(func, mod))
      continue;
    StaticLocalOwner owner{.inst_prefix = inst_prefix_, .subroutine = func};
    specializing_code_.push_back(owner);
    if (!StaticInitsOf(func).empty()) static_local_owners_.push_back(owner);
  }
  for (const RtlirGenBlockSubroutine& sub : mod->gen_block_subroutines) {
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

// §8.25 (printed page 204 of IEEE 1800-2023) makes each specialization a type
// of its own, which §8.9 (printed 186) and §10.5 (printed 256) give static
// variables set before any procedure starts. The specializations the lowering
// met in declarations and typedefs exist by now; those the code of the
// procedures, the subroutines and the classes' methods names are made here,
// before InitializeStaticLocals, each standing where its code runs. Made when
// the code first ran, `C#(3)::s` read `static int s = g;` with g as the
// procedures had left it.
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

// §10.5 (printed page 256) sets a static variable's declaration initializer
// before any initial or always procedure starts, and §6.21 makes a local of a
// block, a task or a function declared `static` one such variable. Each is
// made here, standing in the instance and the generate block its owner was
// lowered in and through the path its declaration takes when it runs -- the
// subroutine's static frame for a task's or a function's (ExecFuncVarDecl),
// the frame of the declaration's own for a procedure's (ExecVarDeclImpl) --
// so that the declaration finds it there when it runs and leaves its value as
// it is. Made when the declaration first ran, `static int s = g;` read a g
// the procedures had changed by then. The static variables of a procedure's
// named blocks are made last, each under its hierarchical name as well, so
// that `inner.x = 3`, written before the block `inner` has run, lands in the
// variable the block then reads (§6.21 and §23.6); made when the block first
// ran, the write found no variable and was lost.
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
