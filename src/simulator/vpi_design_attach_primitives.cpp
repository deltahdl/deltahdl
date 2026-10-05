#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/packed_range.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §28.2 to §28.6 with §37.35: what a gate or switch keyword makes a
// primitive - its vpiPrimType, whether it is a switch rather than a gate, and
// how its terminals run: `outputs` leading ones that are outputs (-1 for all
// but the last, the buf and not gates' form), and `inouts` for a switch whose
// leading two are bidirectional.
struct PrimShape {
  int prim_type = 0;
  bool is_switch = false;
  int outputs = 1;
  bool inouts = false;
};

PrimShape ShapeOf(GateKind kind) {
  switch (kind) {
    case GateKind::kAnd:
      return {vpiAndPrim};
    case GateKind::kNand:
      return {vpiNandPrim};
    case GateKind::kOr:
      return {vpiOrPrim};
    case GateKind::kNor:
      return {vpiNorPrim};
    case GateKind::kXor:
      return {vpiXorPrim};
    case GateKind::kXnor:
      return {vpiXnorPrim};
    case GateKind::kBuf:
      return {vpiBufPrim, false, -1};
    case GateKind::kNot:
      return {vpiNotPrim, false, -1};
    case GateKind::kBufif0:
      return {vpiBufif0Prim};
    case GateKind::kBufif1:
      return {vpiBufif1Prim};
    case GateKind::kNotif0:
      return {vpiNotif0Prim};
    case GateKind::kNotif1:
      return {vpiNotif1Prim};
    case GateKind::kTran:
      return {vpiTranPrim, true, 0, true};
    case GateKind::kRtran:
      return {vpiRtranPrim, true, 0, true};
    case GateKind::kTranif0:
      return {vpiTranif0Prim, true, 0, true};
    case GateKind::kTranif1:
      return {vpiTranif1Prim, true, 0, true};
    case GateKind::kRtranif0:
      return {vpiRtranif0Prim, true, 0, true};
    case GateKind::kRtranif1:
      return {vpiRtranif1Prim, true, 0, true};
    case GateKind::kNmos:
      return {vpiNmosPrim, true};
    case GateKind::kPmos:
      return {vpiPmosPrim, true};
    case GateKind::kRnmos:
      return {vpiRnmosPrim, true};
    case GateKind::kRpmos:
      return {vpiRpmosPrim, true};
    case GateKind::kCmos:
      return {vpiCmosPrim, true};
    case GateKind::kRcmos:
      return {vpiRcmosPrim, true};
    case GateKind::kPullup:
      return {vpiPullupPrim};
    case GateKind::kPulldown:
      return {vpiPulldownPrim};
  }
  return {};
}

// The direction of terminal `index` of `count` a primitive of `shape` has:
// §28.4's buf and not gates drive every terminal but the last, a pullup or
// pulldown (§28.10) every terminal, a bidirectional switch (§28.8) passes
// both ends of its channel, and every other primitive drives its first.
int TerminalDirection(const PrimShape& shape, std::size_t index,
                      std::size_t count) {
  if (shape.inouts) return index < 2 ? kVpiInout : kVpiInput;
  if (shape.prim_type == vpiPullupPrim || shape.prim_type == vpiPulldownPrim) {
    return kVpiOutput;
  }
  if (shape.outputs < 0) return index + 1 < count ? kVpiOutput : kVpiInput;
  return index < static_cast<std::size_t>(shape.outputs) ? kVpiOutput
                                                         : kVpiInput;
}

// Where a primitive is instantiated: the instance, keyed under `prefix` among
// the run's `objects`, whose names its terminals' expressions resolve in.
struct PrimSite {
  VpiObject* instance;
  const std::string& prefix;
  const VpiObjectMap& objects;
};

// §37.35: a gate or switch of `kind` hung from `instance`, named `name`,
// reporting its primitive type and as its size the number of its inputs
// (detail 1), with a prim term per terminal in the order written - its
// direction, its index from zero (detail 3) and the expression it connects,
// `terminals` giving each in turn.
VpiObject* MakePrimitiveObject(GateKind kind, std::string_view name,
                               const std::vector<VpiObject*>& terminals,
                               VpiObject* instance,
                               const VpiAttachBuild& build) {
  const PrimShape kShape = ShapeOf(kind);
  VpiObject* prim = build.alloc();
  prim->type = kShape.is_switch ? vpiSwitch : vpiGate;
  prim->prim_type = kShape.prim_type;
  prim->parent = instance;
  if (!name.empty()) {
    prim->name = build.keep(std::string(name));
    prim->full_name = VpiScopedFullName(instance, name);
  }
  instance->children.push_back(prim);
  const std::size_t kCount = terminals.size();
  int inputs = 0;
  for (std::size_t i = 0; i < kCount; ++i) {
    VpiObject* term = build.alloc();
    term->type = vpiPrimTerm;
    term->parent = prim;
    term->index = static_cast<int>(i);
    term->direction = TerminalDirection(kShape, i, kCount);
    if (term->direction == kVpiInput) ++inputs;
    if (terminals[i] != nullptr) term->children.push_back(terminals[i]);
    prim->children.push_back(term);
  }
  prim->size = inputs;
  return prim;
}

// The expressions `item`'s terminals are written as at `site`.
std::vector<VpiObject*> TerminalObjects(const ModuleItem& item,
                                        const PrimSite& site, SimContext& ctx,
                                        const VpiAttachBuild& build) {
  std::vector<VpiObject*> terminals;
  terminals.reserve(item.gate_terminals.size());
  for (const Expr* terminal : item.gate_terminals) {
    terminals.push_back(
        VpiInstanceExpression(terminal, site.objects, site.prefix, ctx, build));
  }
  return terminals;
}

// §28.3.6: what one element of an instance array connects to: the bit at
// `offset` of a terminal as wide as the array (`length` elements), the
// rightmost element taking the least significant bit, and a terminal of any
// other width whole.
VpiObject* ElementTerminal(VpiObject* whole, int64_t offset, int64_t length) {
  if (whole == nullptr || whole->size != length || length <= 1) return whole;
  for (VpiObject* bit : whole->children) {
    if ((bit->type == vpiNetBit || bit->type == vpiRegBit) &&
        bit->bit_offset == offset) {
      return bit;
    }
  }
  return whole;
}

// §37.11 with §28.3.6: the instance array of gates or switches `item`
// declares at `site`, a gate or switch array over a primitive per element,
// each named by its index and reaching it (§37.35 detail 4).
void MakePrimitiveArray(const ModuleItem& item, const PrimSite& site,
                        SimContext& ctx, const VpiAttachBuild& build) {
  const PackedRange kRange = [&] {
    InstancePrefixOverride scope(ctx.InstancePrefixOverride(),
                                 site.prefix.empty() ? "" : site.prefix + ".");
    return VpiEvaluatedRange(item.inst_range_left, item.inst_range_right, ctx);
  }();
  const int64_t kLength = kRange.HighIndex() - kRange.LowIndex() + 1;
  VpiObject* array = VpiMakeInstanceArray(
      site.instance,
      ShapeOf(item.gate_kind).is_switch ? vpiSwitchArray : vpiGateArray,
      item.gate_inst_name, kRange, build);
  const std::vector<VpiObject*> kWhole =
      TerminalObjects(item, site, ctx, build);
  for (int64_t index = kRange.LowIndex(); index <= kRange.HighIndex();
       ++index) {
    std::vector<VpiObject*> terminals;
    terminals.reserve(kWhole.size());
    for (VpiObject* whole : kWhole) {
      terminals.push_back(
          ElementTerminal(whole, kRange.OffsetOf(index), kLength));
    }
    const std::string kName =
        std::string(item.gate_inst_name) + "[" + std::to_string(index) + "]";
    VpiAddArrayElement(array,
                       MakePrimitiveObject(item.gate_kind, kName, terminals,
                                           site.instance, build),
                       index, build);
  }
}

}  // namespace

void AttachPrimitives(const RtlirDesign* design, const VpiObjectMap& objects,
                      SimContext& ctx, const VpiAttachBuild& build) {
  // §37.35: an instance reaches the gates and switches it instantiates, each
  // with its terminals. RtlirModule::gate_insts kept each instantiation, and
  // no pass read it, so vpiPrimitive reached nothing for any design.
  WalkInstanceObjects(design, objects,
                      [&](const RtlirModule* mod, const std::string& prefix,
                          VpiObject* instance) {
                        for (const ModuleItem* item : mod->gate_insts) {
                          if (item == nullptr) continue;
                          const PrimSite kSite{instance, prefix, objects};
                          // §28.3.6: an instantiation declaring a range is an
                          // instance array.
                          if (item->inst_range_left != nullptr &&
                              item->inst_range_right != nullptr) {
                            MakePrimitiveArray(*item, kSite, ctx, build);
                            continue;
                          }
                          MakePrimitiveObject(
                              item->gate_kind, item->gate_inst_name,
                              TerminalObjects(*item, kSite, ctx, build),
                              instance, build);
                        }
                      });
}

}  // namespace delta
