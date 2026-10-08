#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/packed_range.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_primitives.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §28.2 to §28.6, §29.8 and §37.35: what a primitive is - the definition it is
// an instance of (a gate or switch keyword, or a UDP's name), its vpiPrimType,
// its object type (a gate, a switch or a udp), and how its terminals run:
// `outputs` leading ones that are outputs (-1 for all but the last, the buf and
// not gates' form), and `inouts` for a switch whose leading two are
// bidirectional.
struct PrimShape {
  std::string_view definition;
  int prim_type = 0;
  int type = vpiGate;
  int outputs = 1;
  bool inouts = false;
};

PrimShape ShapeOf(GateKind kind) {
  switch (kind) {
    case GateKind::kAnd:
      return {"and", vpiAndPrim};
    case GateKind::kNand:
      return {"nand", vpiNandPrim};
    case GateKind::kOr:
      return {"or", vpiOrPrim};
    case GateKind::kNor:
      return {"nor", vpiNorPrim};
    case GateKind::kXor:
      return {"xor", vpiXorPrim};
    case GateKind::kXnor:
      return {"xnor", vpiXnorPrim};
    case GateKind::kBuf:
      return {"buf", vpiBufPrim, vpiGate, -1};
    case GateKind::kNot:
      return {"not", vpiNotPrim, vpiGate, -1};
    case GateKind::kBufif0:
      return {"bufif0", vpiBufif0Prim};
    case GateKind::kBufif1:
      return {"bufif1", vpiBufif1Prim};
    case GateKind::kNotif0:
      return {"notif0", vpiNotif0Prim};
    case GateKind::kNotif1:
      return {"notif1", vpiNotif1Prim};
    case GateKind::kTran:
      return {"tran", vpiTranPrim, vpiSwitch, 0, true};
    case GateKind::kRtran:
      return {"rtran", vpiRtranPrim, vpiSwitch, 0, true};
    case GateKind::kTranif0:
      return {"tranif0", vpiTranif0Prim, vpiSwitch, 0, true};
    case GateKind::kTranif1:
      return {"tranif1", vpiTranif1Prim, vpiSwitch, 0, true};
    case GateKind::kRtranif0:
      return {"rtranif0", vpiRtranif0Prim, vpiSwitch, 0, true};
    case GateKind::kRtranif1:
      return {"rtranif1", vpiRtranif1Prim, vpiSwitch, 0, true};
    case GateKind::kNmos:
      return {"nmos", vpiNmosPrim, vpiSwitch};
    case GateKind::kPmos:
      return {"pmos", vpiPmosPrim, vpiSwitch};
    case GateKind::kRnmos:
      return {"rnmos", vpiRnmosPrim, vpiSwitch};
    case GateKind::kRpmos:
      return {"rpmos", vpiRpmosPrim, vpiSwitch};
    case GateKind::kCmos:
      return {"cmos", vpiCmosPrim, vpiSwitch};
    case GateKind::kRcmos:
      return {"rcmos", vpiRcmosPrim, vpiSwitch};
    case GateKind::kPullup:
      return {"pullup", vpiPullupPrim};
    case GateKind::kPulldown:
      return {"pulldown", vpiPulldownPrim};
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

// §37.35: a primitive of `shape` hung from `instance`, named `name`, reporting
// its definition name, its primitive type and as its size the number of its
// inputs (detail 1), with a prim term per terminal in the order written - its
// direction, its index from zero (detail 3) and the expression it connects,
// `terminals` giving each in turn.
VpiObject* MakePrimitiveObject(const PrimShape& shape, std::string_view name,
                               const std::vector<VpiObject*>& terminals,
                               VpiObject* instance,
                               const VpiAttachBuild& build) {
  VpiObject* prim = build.alloc();
  prim->type = shape.type;
  prim->def_name = std::string(shape.definition);
  prim->prim_type = shape.prim_type;
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
    term->direction = TerminalDirection(shape, i, kCount);
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
      ShapeOf(item.gate_kind).type == vpiSwitch ? vpiSwitchArray : vpiGateArray,
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
                       MakePrimitiveObject(ShapeOf(item.gate_kind), kName,
                                           terminals, site.instance, build),
                       index, build);
  }
}

// §29.8 with §37.35: the udp the instantiation `inst` of a UDP makes at `site`,
// its output terminal first and its inputs after it as §29.8 writes them, and
// reaching the udp defn `defn` of the UDP it instantiates.
void MakeUdpObject(const RtlirUdpInst& inst, const PrimSite& site,
                   VpiObject* defn, SimContext& ctx,
                   const VpiAttachBuild& build) {
  std::vector<VpiObject*> terminals;
  terminals.reserve(inst.inputs.size() + 1);
  terminals.push_back(VpiInstanceExpression(inst.output, site.objects,
                                            site.prefix, ctx, build));
  for (const Expr* input : inst.inputs) {
    terminals.push_back(
        VpiInstanceExpression(input, site.objects, site.prefix, ctx, build));
  }
  const PrimShape kShape{inst.decl->name,
                         inst.decl->is_sequential ? vpiSeqPrim : vpiCombPrim,
                         vpiUdp};
  MakePrimitiveObject(kShape, inst.name, terminals, site.instance, build)
      ->udp_defn = defn;
}

}  // namespace

void AttachPrimitives(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiUdpDefnOf& udp_defn_of, SimContext& ctx,
                      const VpiAttachBuild& build) {
  // §37.35: an instance reaches the gates, switches and udps it instantiates,
  // each with its terminals. RtlirModule::gate_insts kept each gate and switch
  // instantiation and udp_insts each UDP one, and no pass read either, so
  // vpiPrimitive reached nothing for any design.
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
                              ShapeOf(item->gate_kind), item->gate_inst_name,
                              TerminalObjects(*item, kSite, ctx, build),
                              instance, build);
                        }
                        for (const RtlirUdpInst& inst : mod->udp_insts) {
                          if (inst.decl == nullptr) continue;
                          MakeUdpObject(inst, {instance, prefix, objects},
                                        udp_defn_of(inst.decl), ctx, build);
                        }
                      });
}

}  // namespace delta
