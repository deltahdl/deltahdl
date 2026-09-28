#include "simulator/lowerer_child.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"

namespace delta {

void Lowerer::CreateChildModuleVariables(const std::string& inst_prefix,
                                         const RtlirModule* resolved) {
  for (const auto& var : resolved->variables) {
    // The prefixed name is interned in the arena because it is the key every
    // map LowerVar records this declaration in stores the variable under, and
    // each holds the key rather than a copy of it.
    auto* name =
        arena_.Create<std::string>(inst_prefix + std::string(var.name));
    LowerVar(*name, var);
  }
}

static void CreateChildModulePorts(const std::string& inst_prefix,
                                   const RtlirModule* resolved, SimContext& ctx,
                                   Arena& arena) {
  // CreatePortStorage interns the prefixed name in the arena because it is the
  // key both SimContext::CreateVariable and VcdDumpState::SetVcdVarKind store
  // the port under, and each holds the key rather than a copy of it.
  for (const auto& port : resolved->ports) {
    CreatePortStorage(inst_prefix, port, ctx, arena);
  }
}

// Whether `name` is one of the module's ports. A port's net is the parent's,
// reached through the binding CreateChildModulePorts makes, so the child does
// not own one of its own under its prefix.
static bool NetNamesAPortOf(const RtlirModule* mod, std::string_view name) {
  for (const auto& port : mod->ports) {
    if (port.name == name) return true;
  }
  return false;
}

// Whether `child` owns `net` and so materializes it under its instance prefix.
//
// An interface keeps every one of its nets, ports included, because §25.3.2
// has its members shared through the port by reference rather than driven
// across it. A regular module's port is the parent's net, reached through the
// binding CreateChildModulePorts makes, so a same-named net materialized here
// would shadow that outer net and the assign would never reach it. §23.9's
// module boundary makes every other net of an instantiated module its own,
// with one exception a nested declaration brings: §23.4 has the outer name
// space visible to a module declared and instantiated in the same scope, so a
// name a continuous assignment or port connection inside it writes may be one
// declared around it, and the net Elaborator::MaybeCreateImplicitNet
// (src/elaborator/elaborator_items.cpp) pushed for that reference stands for
// the outer object -- materialized under the instance it would shadow that
// object and take the assignment with it. The elaborator, which sees the
// enclosing declarations, marks such a net with RtlirNet::refers_outward, and
// that mark alone is what leaves a net to the outer scope: a net the nested
// module declares for itself is its own, §23.4's ff2 encapsulating its `wire
// q2`, and so is an implicit net of a name no enclosing module declares,
// which §6.10 gives to the scope the reference appears in -- one per instance,
// as §36.10 has for m1.w and m2.w. RtlirNet::loc told the declared nets from
// the implicit ones before, and put that last kind with the outer scope.
static bool ChildOwnsNet(const RtlirModuleInst& child, const RtlirNet& net) {
  const RtlirModule* resolved = child.resolved;
  if (resolved->is_interface) return true;
  if (NetNamesAPortOf(resolved, net.name)) return false;
  return !net.refers_outward;
}

// 25.3.2: a child instance's nets - e.g. an interface `wire` member accessed
// through a port by reference - must be materialized under the child's instance
// prefix, just like its variables. LowerModule does this for the top via
// RegisterModuleNets; child instances need the prefixed form so a continuous
// assign driven through the port resolves onto the shared net.
//
// §36.10 is why a regular module's nets are materialized too: a module m
// holding a wire w and instantiated twice as m1 and m2 has m1.w and m2.w as
// two distinct objects. A net a module declares for itself has one object
// per instance, and with none created there was nothing under either name --
// the design held the declaration and no storage for it. §23.4 makes a nested
// declaration's instances such instances too: `and2 u1(...), u2(...), u3(...)`
// of a module declared beside them are three, each with the nets it declares.
// ChildOwnsNet says which nets are the child's own to materialize.
static void CreateChildModuleNets(const std::string& inst_prefix,
                                  const RtlirModuleInst& child, SimContext& ctx,
                                  Arena& arena) {
  const RtlirModule* resolved = child.resolved;
  for (const auto& net : resolved->nets) {
    if (!ChildOwnsNet(child, net)) continue;
    auto* name = arena.Create<std::string>(inst_prefix + std::string(net.name));
    CreateDeclaredNet(*name, net, resolved->timescale, ctx, arena);
  }
}

// §10.11: an alias statement makes the nets it lists one physical net, each a
// driver and a receiver of the others, and §23.9 resolves the bare names it
// writes in the module that declares them, so the alias of a module
// instantiated twice joins each instance's own nets. The nets of an instance
// are created under the instance's prefix by CreateChildModuleNets and the
// top's under their bare names by RegisterModuleNets, so each name the alias
// writes is keyed the same way: inst_prefix_ is empty for the top. Registered
// under the bare name alone, an instance's alias found the top's like-named
// net or none, and an instance's nets stayed apart. The prefixed name is
// interned in the arena because the variable and net maps hold the key rather
// than a copy of it.
void Lowerer::LowerAliases(const RtlirModule* mod) {
  for (const auto& alias : mod->aliases) {
    if (alias.nets.size() < 2) continue;
    std::string_view primary;
    for (auto* net : alias.nets) {
      if (net->kind != ExprKind::kIdentifier) continue;
      const std::string& name =
          *arena_.Create<std::string>(inst_prefix_ + std::string(net->text));
      if (primary.empty()) {
        primary = name;
        continue;
      }
      // The aliased nets share one resolved storage. Both the variable map,
      // which reads go through, and the net map, which continuous-assign
      // driver resolution goes through, are redirected; otherwise a driver on
      // the non-primary net writes a Variable the alias never sees.
      ctx_.AliasVariable(name, primary);
      ctx_.AliasNet(name, primary);
    }
  }
}

// §23.3.1 (printed page 740): "A top-level module is implicitly instantiated
// once, and its instance name is the same as the module name", and each such
// instance is a scope of its own (§23.9), so two tops' declarations of one
// name are two objects. The first top's are keyed under their bare names, as
// every lookup from the top of the design expects; a later top is lowered as
// an instance of that name, its declarations keyed under "name." as an
// instance's are under its path, so `int x` in t1 and in t2 are t1's x and
// t2.x. Keyed alike, the second top's x replaced the first's in the one table
// both were written to, and each read the other's value.
void Lowerer::LowerParallelTop(const RtlirModule* mod) {
  ctx_.RegisterParallelTop(mod->name);
  RtlirModuleInst inst;
  inst.module_name = mod->name;
  inst.inst_name = mod->name;
  inst.simple_inst_name = mod->name;
  // The instance only reads its module; RtlirModuleInst holds one to write.
  inst.resolved = const_cast<RtlirModule*>(mod);
  LowerChildInstance(inst);
}

// §23.6 with §27.4 (printed page 820): an instance a generate block holds is
// named through the block instance, `g[0].pi`, while its storage is keyed on
// the one flat name the elaborator gives it (RtlirModuleInst::inst_name,
// "g_0_pi"). The path is the parent's path, the block instances and the name
// as written, recorded for the child's key wherever it differs from the key,
// so an instance below one inside a generate block is named through it too.
static void RegisterChildInstancePath(const std::string& parent_prefix,
                                      const std::string& child_prefix,
                                      const RtlirModuleInst& child,
                                      SimContext& ctx) {
  std::string path(ctx.FindInstancePath(parent_prefix));
  if (path.empty()) {
    path = parent_prefix;
    if (!path.empty()) path.pop_back();
  }
  std::string gen = GenBlockName(child.gen_block_path);
  for (std::string_view level :
       {std::string_view(gen), child.simple_inst_name.empty()
                                   ? child.inst_name
                                   : child.simple_inst_name}) {
    if (level.empty()) continue;
    if (!path.empty()) path += '.';
    path += level;
  }
  if (path + "." != child_prefix) ctx.RegisterInstancePath(child_prefix, path);
}

void Lowerer::LowerChildModules(const RtlirModule* mod) {
  for (const auto& child : mod->children) {
    if (child.resolved) LowerChildInstance(child);
  }
}

void Lowerer::LowerChildBody(const RtlirModule* mod) {
  // §10.11: the instance's alias statements join the nets LowerChildInstance
  // created, ahead of the processes and continuous assignments that drive and
  // read them, as LowerModule orders the top's.
  LowerAliases(mod);
  uint32_t child_block_id = mod->is_program ? next_program_block_id_++ : 0;
  LowerProcesses(mod->processes, mod->is_program, child_block_id);
  for (const auto& ca : mod->assigns) {
    LowerContAssign(ca, mod->is_program);
  }
  for (const auto& sw : mod->bidir_switches) {
    LowerBidirSwitch(sw, mod->is_program);
  }
  // §29.8: a primitive instance written in this child drives its output
  // terminal wherever the child sits, so it is lowered under the child's
  // prefix beside the child's continuous assignments.
  for (const auto& udp_inst : mod->udp_insts) {
    LowerUdpInst(udp_inst, mod->is_program);
  }
  // §14.3: a clocking block belongs to the instance that declares it, so this
  // instance's blocks are registered under this instance's prefix, beside its
  // processes. Lowerer::AttachDesignClocking arms them all once the whole
  // design is lowered.
  LowerClockingBlocks(mod);

  LowerChildModules(mod);
}

void Lowerer::LowerChildInstance(const RtlirModuleInst& child) {
  auto saved_prefix = inst_prefix_;
  auto child_prefix = inst_prefix_ + std::string(child.inst_name) + ".";
  RegisterChildInstancePath(saved_prefix, child_prefix, child, ctx_);
  inst_prefix_ = child_prefix;
  // §23.9: the names a declaration initializer writes resolve within the
  // instance the declaration sits in. That initializer is evaluated here,
  // before any process exists to carry the instance, so the context is told
  // which instance is being built. It moves in step with inst_prefix_
  // throughout this function because the two mean the same thing.
  ctx_.SetLoweringInstancePrefix(inst_prefix_);
  // §23.4: a module, program or interface declared inside this one sees the
  // names declared here, so its scope keeps searching outward rather than
  // stopping at the §23.9 module boundary.
  if (child.is_nested_decl) ctx_.RegisterNestedDeclScope(inst_prefix_);

  RegisterInstanceKeyBinding(inst_prefix_, child.resolved->library,
                             child.resolved->name, ctx_);
  LowerParams(child.resolved);
  // §30.3: the child's specify blocks belong to this instance, so they are
  // recorded under this instance's prefix. Lower registers them once every
  // module is lowered, because a module path delay may be written as a
  // specparam and this instance's specparam variables are created below.
  RecordSpecifyScope(child.resolved);
  // §26.3: an import makes a package's names visible "within the current
  // scope", and the scope is the one that writes the import. A module writes
  // its own imports whether it is the top or an instance, so the instance's
  // are lowered here, and before its variables as LowerModule orders the
  // top's: §6.8 sets a variable's initial value as part of its declaration,
  // a reference the declaring scope makes with the imported names already
  // visible. A name the instance declares itself is left to the declaration
  // by LowerImports (§26.5).
  LowerImports(child.resolved);
  // §6.19 with §23.3: an enumeration the instance's module declares is a type
  // of that module wherever it is instantiated, registered as LowerModule
  // registers the top's, so `name()` and `next()` answer on a variable of it.
  RegisterEnumTypes(child.resolved);
  RegisterParamEnumTypes(child.resolved);
  // §8 with §23.3: a class the instance's module declares is a type of that
  // module wherever it is instantiated, registered as LowerModule registers
  // the top's -- before the variables, so a handle's `C h = new;` finds it
  // -- and once, a second instance of the module declaring the same class.
  std::vector<const ClassDecl*> fresh_classes;
  for (auto* cls : child.resolved->class_decls) {
    const ClassTypeInfo* known = ctx_.FindClassType(cls->name);
    if (known != nullptr && known->decl == cls) continue;
    RegisterClassDecl(cls, child.resolved->function_decls);
    fresh_classes.push_back(cls);
  }
  CreateChildModuleVariables(inst_prefix_, child.resolved);
  for (const ClassDecl* cls : fresh_classes) InitClassStaticProperties(cls);
  CreateChildModulePorts(inst_prefix_, child.resolved, ctx_, arena_);
  CreateChildModuleNets(inst_prefix_, child, ctx_, arena_);
  // 21.2.1.5: register the child instance's tasks/functions so a call within
  // its own body resolves (and %m composes the instance + subroutine path);
  // LowerModule registers these for the top only.
  RegisterModuleSubroutines(child.resolved, ctx_);
  // §13.3 with §23.6: and under the instance's own prefixed key, which an
  // enable by hierarchical name from another instance resolves by.
  RegisterInstanceSubroutines(child.resolved, inst_prefix_, ctx_, arena_);
  // §27.4 with §13.4: and those of the instance's generate blocks under
  // the instance's key too, "u1.blk[1].triple".
  RegisterGenBlockSubroutines(child.resolved, inst_prefix_, inst_prefix_, ctx_,
                              arena_);
  // §35.5.4: an import declaration defines the subroutine in the scope
  // that writes it, an instantiated module, interface or program as much as
  // the top; the top's are registered by LowerModule.
  RegisterModuleDpiImports(child.resolved, ctx_);
  RecordSubroutineAssertionSampleScopes(child.resolved);
  // §16.12.1: an assertion of the instance that instantiates a property or
  // sequence the instance's module declares expands it at the run, so the
  // declarations are registered as the top's are.
  RegisterModuleSequenceDecls(child.resolved, ctx_);

  // Port connections resolve in the parent scope (see LowerPortBindings),
  // then restore the child prefix for the child's own body.
  inst_prefix_ = saved_prefix;
  ctx_.SetLoweringInstancePrefix(inst_prefix_);
  LowerPortBindings(child, child.resolved->is_program);
  inst_prefix_ = child_prefix;
  ctx_.SetLoweringInstancePrefix(inst_prefix_);

  LowerChildBody(child.resolved);

  inst_prefix_ = saved_prefix;
  ctx_.SetLoweringInstancePrefix(inst_prefix_);
}

}  // namespace delta
