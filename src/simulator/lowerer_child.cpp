#include "simulator/lowerer_child.h"

#include <cstdint>
#include <string>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/net.h"
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
  for (const auto& port : resolved->ports) {
    // The prefixed name is interned in the arena because it is the key both
    // SimContext::CreateVariable and SimContext::SetVcdVarKind store the port
    // under, and each holds the key rather than a copy of it.
    auto* name =
        arena.Create<std::string>(inst_prefix + std::string(port.name));
    CreatePortVariable(*name, port, ctx, arena);
  }
}

// 25.3.2: a child instance's nets - e.g. an interface `wire` member accessed
// through a port by reference - must be materialized under the child's instance
// prefix, just like its variables. LowerModule does this for the top via
// RegisterModuleNets; child instances need the prefixed form so a continuous
// assign driven through the port resolves onto the shared net.
static void CreateChildModuleNets(const std::string& inst_prefix,
                                  const RtlirModule* resolved, SimContext& ctx,
                                  Arena& arena) {
  for (const auto& net : resolved->nets) {
    auto* name = arena.Create<std::string>(inst_prefix + std::string(net.name));
    auto* created = ctx.CreateNet(
        *name, net.net_type, net.width,
        NetSpec{net.charge_strength, net.decay_ticks, net.is_user_nettype,
                net.resolve_func, net.is_signed});
    RecordPackedRange(net.dtype, created->resolved, ctx, arena);
  }
}

void Lowerer::LowerChildModules(const RtlirModule* mod) {
  for (const auto& child : mod->children) {
    if (!child.resolved) continue;
    auto saved_prefix = inst_prefix_;
    auto child_prefix = inst_prefix_ + std::string(child.inst_name) + ".";
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
    CreateChildModuleVariables(inst_prefix_, child.resolved);
    CreateChildModulePorts(inst_prefix_, child.resolved, ctx_, arena_);
    // 25.3.2: only an interface instance owns nets that must be materialized
    // under its prefix (its `wire` members, shared through ports by reference).
    // A regular module or program instead drives nets declared in an enclosing
    // scope through a continuous assign; materializing a same-named net here
    // would shadow that outer net so the assign never reaches it.
    if (child.resolved->is_interface) {
      CreateChildModuleNets(inst_prefix_, child.resolved, ctx_, arena_);
    }
    // 21.2.1.5: register the child instance's tasks/functions so a call within
    // its own body resolves (and %m composes the instance + subroutine path);
    // LowerModule registers these for the top only.
    RegisterModuleSubroutines(child.resolved, ctx_);

    // Port connections resolve in the parent scope (see LowerPortBindings),
    // then restore the child prefix for the child's own body.
    inst_prefix_ = saved_prefix;
    ctx_.SetLoweringInstancePrefix(inst_prefix_);
    LowerPortBindings(child, child.resolved->is_program);
    inst_prefix_ = child_prefix;
    ctx_.SetLoweringInstancePrefix(inst_prefix_);

    uint32_t child_block_id =
        child.resolved->is_program ? next_program_block_id_++ : 0;
    LowerProcesses(child.resolved->processes, child.resolved->is_program,
                   child_block_id);
    for (const auto& ca : child.resolved->assigns) {
      LowerContAssign(ca, child.resolved->is_program);
    }

    LowerChildModules(child.resolved);

    inst_prefix_ = saved_prefix;
    ctx_.SetLoweringInstancePrefix(inst_prefix_);
  }
}

}  // namespace delta
