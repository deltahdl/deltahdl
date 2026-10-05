#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §37.48 with §14.3: the vpiDirection of a clocking signal declared
// `direction`.
int ClockingDirectionOf(Direction direction) {
  switch (direction) {
    case Direction::kInput:
      return kVpiInput;
    case Direction::kOutput:
      return kVpiOutput;
    case Direction::kInout:
      return kVpiInout;
    default:
      return 0;
  }
}

// Where a clocking block is declared: the instance, keyed under `prefix` among
// the run's `objects`, whose names its signals and event resolve in.
struct ClockingSite {
  VpiObject* instance;
  const std::string& prefix;
  const VpiObjectMap& objects;
};

// §37.48 detail 4 with §14.3: what a clocking signal stands for - the
// expression its hierarchical_expression is written as, and otherwise the
// signal of the scope it is named after.
VpiObject* SignalTarget(const ClockingSignalDecl& signal,
                        const ClockingSite& site, SimContext& ctx,
                        const VpiAttachBuild& build) {
  if (signal.hier_expr != nullptr) {
    return VpiInstanceExpression(signal.hier_expr, site.objects, site.prefix,
                                 ctx, build);
  }
  return FindObjectForFlatName(site.objects,
                               VpiFlatName(site.prefix, signal.name));
}

// §37.48: the clocking block `item` declares at `site`, named as declared,
// reaching through vpiClockingEvent the event control its clocking event makes
// and an io decl per clocking signal - its name, its direction and through
// vpiExpr (detail 4) what it stands for - and marked where §14.12 made it the
// scope's default clocking or §14.14 its global clocking.
void MakeClockingBlock(const ModuleItem& item, const ClockingSite& site,
                       SimContext& ctx, const VpiAttachBuild& build) {
  VpiObject* block = build.alloc();
  block->type = vpiClockingBlock;
  block->parent = site.instance;
  if (!item.name.empty()) {
    block->name = build.keep(std::string(item.name));
    block->full_name = VpiScopedFullName(site.instance, item.name);
  }
  block->default_clocking = item.is_default_clocking;
  block->global_clocking = item.is_global_clocking;
  site.instance->children.push_back(block);
  const VpiStmtBuild kWith{build,
                           [&](const Expr* expr) {
                             return VpiInstanceExpression(
                                 expr, site.objects, site.prefix, ctx, build);
                           },
                           nullptr, nullptr};
  VpiObject* event = build.alloc();
  event->type = vpiEventControl;
  event->parent = block;
  VpiObject* condition = VpiEventCondition(item.clocking_event, kWith);
  if (condition != nullptr) event->children.push_back(condition);
  block->children.push_back(event);
  for (const ClockingSignalDecl& signal : item.clocking_signals) {
    VpiObject* decl = build.alloc();
    decl->type = vpiClockingIODecl;
    decl->parent = block;
    decl->name = build.keep(std::string(signal.name));
    decl->direction = ClockingDirectionOf(signal.direction);
    VpiObject* target = SignalTarget(signal, site, ctx, build);
    if (target != nullptr) decl->children.push_back(target);
    block->children.push_back(decl);
  }
}

}  // namespace

void AttachClockingBlocks(const RtlirDesign* design,
                          const VpiObjectMap& objects, SimContext& ctx,
                          const VpiAttachBuild& build) {
  // §37.48 with §37.5, §37.6 and §37.9: an instance reaches the clocking blocks
  // it declares, and through vpiDefaultClocking and vpiGlobalClocking the one
  // it named default and the one it named global. RtlirModule::clocking_blocks
  // kept each declaration, and no pass made an object of it, so both relations
  // and vpi_iterate(vpiClockingBlock) reached nothing for any design.
  WalkInstanceObjects(design, objects,
                      [&](const RtlirModule* mod, const std::string& prefix,
                          VpiObject* instance) {
                        for (const ModuleItem* item : mod->clocking_blocks) {
                          if (item == nullptr) continue;
                          MakeClockingBlock(*item, {instance, prefix, objects},
                                            ctx, build);
                        }
                      });
}

}  // namespace delta
