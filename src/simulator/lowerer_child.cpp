#include "simulator/lowerer_child.h"

#include <cstdint>
#include <string>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"

namespace delta {

static void CreateChildModuleVariable(const std::string& inst_prefix,
                                      const RtlirVariable& var, SimContext& ctx,
                                      Arena& arena) {
  auto* name = arena.Create<std::string>(inst_prefix + std::string(var.name));
  uint32_t width = var.class_type_name.empty() ? var.width : 64;
  if (var.is_real && width < 64) width = 64;
  auto* v = ctx.CreateVariable(*name, width);
  if (!var.is_4state && !var.is_event && !var.is_string && !var.is_chandle)
    v->value = MakeLogic4VecVal(arena, width, 0);
  if (var.is_chandle) v->value = MakeLogic4VecVal(arena, width, 0);
  v->is_4state = var.is_4state;
  if (var.is_event) v->is_event = true;
  if (var.is_signed) v->is_signed = true;
  if (var.init_expr) {
    v->value = EvalExpr(var.init_expr, ctx, arena);
  }
}

static void CreateChildModuleVariables(const std::string& inst_prefix,
                                       const RtlirModule* resolved,
                                       SimContext& ctx, Arena& arena) {
  for (const auto& var : resolved->variables) {
    CreateChildModuleVariable(inst_prefix, var, ctx, arena);
  }
}

static void CreateChildModulePorts(const std::string& inst_prefix,
                                   const RtlirModule* resolved, SimContext& ctx,
                                   Arena& arena) {
  for (const auto& port : resolved->ports) {
    auto* name =
        arena.Create<std::string>(inst_prefix + std::string(port.name));
    if (!ctx.FindVariable(*name)) {
      auto* v = ctx.CreateVariable(*name, port.width);
      if (port.is_signed) v->is_signed = true;
    }
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
    ctx.CreateNet(
        *name, net.net_type, net.width,
        NetSpec{net.charge_strength, net.decay_ticks, net.is_user_nettype,
                net.resolve_func, net.is_signed});
  }
}

void Lowerer::LowerChildModules(const RtlirModule* mod) {
  for (const auto& child : mod->children) {
    if (!child.resolved) continue;
    auto saved_prefix = inst_prefix_;
    auto child_prefix = inst_prefix_ + std::string(child.inst_name) + ".";
    inst_prefix_ = child_prefix;

    RegisterInstanceKeyBinding(inst_prefix_, child.resolved->library,
                               child.resolved->name, ctx_);
    LowerParams(child.resolved);
    CreateChildModuleVariables(inst_prefix_, child.resolved, ctx_, arena_);
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
    LowerPortBindings(child, child.resolved->is_program);
    inst_prefix_ = child_prefix;

    uint32_t child_block_id =
        child.resolved->is_program ? next_program_block_id_++ : 0;
    LowerProcesses(child.resolved->processes, child.resolved->is_program,
                   child_block_id);
    for (const auto& ca : child.resolved->assigns) {
      LowerContAssign(ca, child.resolved->is_program);
    }

    LowerChildModules(child.resolved);

    inst_prefix_ = saved_prefix;
  }
}

}  // namespace delta
