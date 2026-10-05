#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
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

// §37.48 detail 1 with §14.4: the edge a clocking skew is written with, as
// vpiInputEdge and vpiOutputEdge report it. The `edge` keyword makes the skew
// both edges'.
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

// §14.4: one clocking skew - the edge and the delay it is written with, either
// absent.
struct Skew {
  Edge edge = Edge::kNone;
  const Expr* delay = nullptr;

  bool Written() const { return edge != Edge::kNone || delay != nullptr; }
};

// Where a clocking block is declared: the scope it stands in - its instance,
// keyed under `prefix` among the run's `objects`, or a generate block instance
// of it whose names `gen_prefixes` carries (§27.4) - in which its signals and
// event resolve.
struct ClockingSite {
  VpiObject* holder;
  VpiObject* instance;
  const std::string& prefix;
  const VpiObjectMap& objects;
  const std::vector<std::string_view>& gen_prefixes;
};

// What a clocking block is built with: its site, the run and the attach.
struct ClockingBuild {
  const ClockingSite& site;
  SimContext& ctx;
  const VpiAttachBuild& build;

  VpiObject* Expression(const Expr* expr) const {
    return VpiGenBlockExpression(
        expr, VpiExprNames{site.objects, site.prefix, site.gen_prefixes}, ctx,
        build);
  }
};

// §37.48 detail 1: the delay of `skew` as vpiInputSkew or vpiOutputSkew
// reaches it from `owner` - the delay expression itself where `bare`, as an io
// decl's output skew is drawn, and otherwise a delay control over it (§37.68).
// Null where the skew writes no delay.
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

// §37.48 detail 1: `owner`'s input and output skews, `input` and `output`.
void SetSkews(VpiObject* owner, const Skew& input, const Skew& output,
              const ClockingBuild& with) {
  owner->input_edge = EdgeOf(input.edge);
  owner->output_edge = EdgeOf(output.edge);
  owner->input_skew = SkewDelay(input, owner, false, with);
  owner->output_skew =
      SkewDelay(output, owner, owner->type == vpiClockingIODecl, with);
}

// §37.48 detail 4 with §14.3: what a clocking signal stands for - the
// expression its hierarchical_expression is written as, and otherwise the
// signal it is named after, found in the scope the block stands in and then in
// those around it up to its instance.
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

// §37.48: the io decl of `block` for `signal`, named as declared, reporting
// its direction, reaching through vpiExpr (detail 4) what it stands for, and
// with the skews §14.4 gives it - its own where it writes one, and otherwise
// the block's default for its direction (`input` and `output`).
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

// §37.48: the clocking block `item` declares, named as declared, reaching
// through vpiClockingEvent the event control its clocking event makes, its
// default skews (detail 1) and an io decl per clocking signal, and marked
// where §14.12 made it the scope's default clocking or §14.14 its global
// clocking.
void MakeClockingBlock(const ModuleItem& item, const ClockingBuild& with) {
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
  const VpiStmtBuild kWith{
      with.build, [&](const Expr* expr) { return with.Expression(expr); },
      nullptr, nullptr};
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
  SetSkews(block, kInput, kOutput, with);
  for (const ClockingSignalDecl& signal : item.clocking_signals) {
    MakeIoDecl(signal, block, kInput, kOutput, with);
  }
}

// The generate block instance that declared the clocking block at `index` of
// `mod`'s clocking blocks, null for one the module declares itself.
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
  // §37.48 with §37.5, §37.6 and §37.9: a scope reaches the clocking blocks it
  // declares, and through vpiDefaultClocking and vpiGlobalClocking the one it
  // named default and the one it named global. A block a generate block
  // declares is that generate block instance's (§37.12, §27.4), one per
  // instance, RtlirModule::gen_block_clocking naming which.
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
              holder, instance, prefix, objects,
              gen == nullptr ? kNoGenPrefixes : gen->gen_block_prefixes};
          MakeClockingBlock(*item, ClockingBuild{kSite, ctx, build});
        }
      });
}

}  // namespace delta
