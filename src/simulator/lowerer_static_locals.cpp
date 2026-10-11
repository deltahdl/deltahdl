#include <algorithm>
#include <string_view>
#include <tuple>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/class_object.h"
#include "simulator/deferred_caller.h"
#include "simulator/eval_function_hier.h"
#include "simulator/eval_function_internal.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"

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

// §13.4.2: the static locals of `owner`'s subroutine, made in its static frame
// as a call makes them (EvalFunctionCall): the frame entered with the
// subroutine's package, and a generate block instance's subroutine with the
// block's loop constants beside them.
void InitSubroutineStatics(const StaticLocalOwner& owner, SimContext& ctx,
                           Arena& arena) {
  const ModuleItem* func = owner.subroutine;
  ctx.PushStaticScope(func->name);
  ctx.EnterSubroutinePackage(func);
  if (owner.gen_block != nullptr) {
    GenBlockSubroutineScope scope;
    scope.consts = owner.gen_block->gen_block_consts;
    SubroutineTarget target;
    target.gen_block = &scope;
    BindGenBlockConsts(target, ctx, arena);
  }
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

// §10.5 with §8.6: the method static locals of the classes `decls` the module
// of the instance `prefix` declares, made standing in that instance, whose
// frames a call keeps under it (SimContext::StaticFrameKey). The classes are
// the ones the instance holds (InstanceClassScope), with each class nested in
// one (§8.23) and each specialization of one made by now (§8.25).
void InitModuleClassMethodStatics(const std::vector<ClassDecl*>& decls,
                                  std::string_view prefix, SimContext& ctx,
                                  Arena& arena) {
  std::vector<ClassTypeInfo*> held = ctx.RegisteredClassTypes(true);
  for (const ClassDecl* decl : decls) {
    std::string_view scope = InstanceClassScope(decl, prefix, held);
    for (const ClassTypeInfo* cls : held) {
      if (cls->package.empty() && cls->instance_scope == scope &&
          OutermostClass(cls)->decl == decl) {
        InitClassMethodStatics(cls, ctx, arena);
      }
    }
  }
}

}  // namespace

void Lowerer::RecordStaticLocalSubroutines(const RtlirModule* mod) {
  if (!mod->class_decls.empty()) {
    static_local_owners_.push_back(
        {.inst_prefix = inst_prefix_, .classes = &mod->class_decls});
  }
  for (const ModuleItem* func : mod->function_decls) {
    if (!func->method_class.empty() || StaticInitsOf(func).empty() ||
        IsGenBlockSubroutine(func, mod))
      continue;
    static_local_owners_.push_back(
        {.inst_prefix = inst_prefix_, .subroutine = func});
  }
  for (const RtlirGenBlockSubroutine& sub : mod->gen_block_subroutines) {
    if (StaticInitsOf(sub.decl).empty()) continue;
    static_local_owners_.push_back({.inst_prefix = inst_prefix_,
                                    .subroutine = sub.decl,
                                    .gen_block = &sub});
  }
}

void Lowerer::RecordStaticLocalProcess(const Process* p, const Stmt* body) {
  if (StaticInitsOf(body).empty()) return;
  static_local_owners_.push_back(
      {.inst_prefix = inst_prefix_, .process = p, .body = body});
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
// the procedures had changed by then.
void Lowerer::InitializeStaticLocals() {
  InitOwnedSubroutineStatics(ctx_, arena_);
  InitPackageClassMethodStatics(ctx_, arena_);
  for (const StaticLocalOwner& owner : static_local_owners_) {
    Process stand_in;
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
}

}  // namespace delta
