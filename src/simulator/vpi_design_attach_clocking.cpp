#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_attribute.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
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

int EdgeOf(Edge edge) {
  switch (edge) {
    case Edge::kPosedge:
      return vpiPosedge;
    case Edge::kNegedge:
      return vpiNegedge;
    case Edge::kEdge:
      return vpiAnyEdge;
    default:
      return vpiNoEdge;
  }
}

struct Skew {
  Edge edge = Edge::kNone;
  const Expr* delay = nullptr;

  bool Written() const { return edge != Edge::kNone || delay != nullptr; }
};

struct ClockingSite {
  VpiObject* holder;
  VpiObject* instance;
  const std::string& prefix;
  const VpiObjectMap& objects;
  const std::vector<std::string_view>& gen_prefixes;
  const RtlirNodeAttributes* attrs = nullptr;
  const RtlirModule* mod = nullptr;
};

struct ClockingBuild {
  const ClockingSite& site;
  SimContext& ctx;
  const VpiAttachBuild& build;
  const VpiCallStand* stand = nullptr;

  VpiObject* Expression(const Expr* expr) const {
    return VpiGenBlockExpression(
        expr,
        VpiExprNames{site.objects, site.prefix, site.gen_prefixes, nullptr,
                     site.attrs, stand},
        ctx, build);
  }
};

VpiObject* SkewDelay(const Skew& skew, VpiObject* owner, bool bare,
                     const ClockingBuild& with) {
  if (skew.delay == nullptr) return nullptr;
  VpiObject* delay = with.Expression(skew.delay);
  if (bare) return delay;
  VpiObject* control = with.build.alloc();
  control->type = vpiDelayControl;
  control->parent = owner;
  if (delay != nullptr) control->children.push_back(delay);
  return control;
}

void SetSkews(VpiObject* owner, const Skew& input, const Skew& output,
              const ClockingBuild& with) {
  owner->input_edge = EdgeOf(input.edge);
  owner->output_edge = EdgeOf(output.edge);
  owner->input_skew = SkewDelay(input, owner, false, with);
  owner->output_skew =
      SkewDelay(output, owner, owner->type == vpiClockingIODecl, with);
}

VpiObject* SignalTarget(const ClockingSignalDecl& signal,
                        const ClockingBuild& with) {
  if (signal.hier_expr != nullptr) return with.Expression(signal.hier_expr);
  for (VpiObject* scope = with.site.holder; scope != nullptr;
       scope = scope->parent) {
    VpiObject* found = ChildNamed(scope, signal.name);
    if (found != nullptr || scope == with.site.instance) return found;
  }
  return nullptr;
}

void MakeIoDecl(const ClockingSignalDecl& signal, VpiObject* block,
                const Skew& input, const Skew& output,
                const ClockingBuild& with) {
  VpiObject* decl = with.build.alloc();
  decl->type = vpiClockingIODecl;
  decl->parent = block;
  decl->name = with.build.keep(std::string(signal.name));
  decl->direction = ClockingDirectionOf(signal.direction);
  VpiObject* target = SignalTarget(signal, with);
  if (target != nullptr) decl->children.push_back(target);
  block->children.push_back(decl);
  const Skew kFirst{signal.skew_edge, signal.skew_delay};
  const Skew kSecond{signal.out_skew_edge, signal.out_skew_delay};
  const bool kOutputOnly = signal.direction == Direction::kOutput;
  const Skew kInput =
      kOutputOnly ? Skew{} : (kFirst.Written() ? kFirst : input);
  const Skew& own_output = kOutputOnly ? kFirst : kSecond;
  const Skew kOutput = signal.direction == Direction::kInput
                           ? Skew{}
                           : (own_output.Written() ? own_output : output);
  SetSkews(decl, kInput, kOutput, with);
}

VpiObject* MakeClockingBlock(const ModuleItem& item,
                             const ClockingBuild& with) {
  VpiObject* holder = with.site.holder;
  VpiObject* block = with.build.alloc();
  block->type = vpiClockingBlock;
  block->parent = holder;
  if (!item.name.empty()) {
    block->name = with.build.keep(std::string(item.name));
    block->full_name = VpiScopedFullName(holder, item.name);
  }
  block->default_clocking = item.is_default_clocking;
  block->global_clocking = item.is_global_clocking;
  holder->children.push_back(block);
  const VpiCallStand kStand{block, with.site.mod};
  const ClockingBuild kInBlock{with.site, with.ctx, with.build, &kStand};
  const VpiStmtBuild kWith{
      with.build, [&](const Expr* expr) { return kInBlock.Expression(expr); },
      nullptr,    nullptr,
      nullptr,    nullptr};
  VpiObject* event = with.build.alloc();
  event->type = vpiEventControl;
  event->parent = block;
  VpiObject* condition = VpiEventCondition(item.clocking_event, kWith);
  if (condition != nullptr) event->children.push_back(condition);
  block->children.push_back(event);
  const Skew kInput{item.default_input_skew_edge,
                    item.default_input_skew_delay};
  const Skew kOutput{item.default_output_skew_edge,
                     item.default_output_skew_delay};
  SetSkews(block, kInput, kOutput, kInBlock);
  for (const ClockingSignalDecl& signal : item.clocking_signals) {
    MakeIoDecl(signal, block, kInput, kOutput, kInBlock);
  }
  return block;
}

const RtlirGenBlockClocking* GenBlockOf(const RtlirModule& mod,
                                        std::size_t index) {
  for (const RtlirGenBlockClocking& entry : mod.gen_block_clocking) {
    if (entry.index == index) return &entry;
  }
  return nullptr;
}

}  // namespace

void AttachClockingBlocks(const RtlirDesign* design,
                          const VpiObjectMap& objects, SimContext& ctx,
                          const VpiAttachBuild& build) {
  const std::vector<std::string_view> kNoGenPrefixes;
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string& prefix,
          VpiObject* instance) {
        for (std::size_t i = 0; i < mod->clocking_blocks.size(); ++i) {
          const ModuleItem* item = mod->clocking_blocks[i];
          const RtlirGenBlockClocking* gen = GenBlockOf(*mod, i);
          VpiObject* holder =
              gen == nullptr ? instance
                             : VpiGenScopeOf(instance, gen->gen_block_path);
          if (item == nullptr || holder == nullptr) continue;
          const ClockingSite kSite{
              holder,
              instance,
              prefix,
              objects,
              gen == nullptr ? kNoGenPrefixes : gen->gen_block_prefixes,
              &mod->node_attrs,
              mod};
          VpiObject* block =
              MakeClockingBlock(*item, ClockingBuild{kSite, ctx, build});
          VpiAttachAttributes(block, VpiNodeAttributes(mod, item), false, ctx,
                              build);
        }
      });
}

void AttachDefaultDisableIffs(const RtlirDesign* design,
                              const VpiObjectMap& objects, SimContext& ctx,
                              const VpiAttachBuild& build) {
  WalkInstanceObjects(design, objects,
                      [&](const RtlirModule* mod, const std::string& prefix,
                          VpiObject* instance) {
                        if (mod->default_disable_iff == nullptr) return;
                        instance->disable_condition =
                            VpiInstanceExpression(mod->default_disable_iff,
                                                  objects, prefix, ctx, build);
                      });
}

}  // namespace delta
