#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/packed_range.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_gate_array_terminals.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_attribute.h"
#include "elaborator/rtlir_primitives.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "simulator/dpi_formal_type.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_source_delay.h"
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
    default:  // GateKind::kPulldown, the one kind left.
      return {"pulldown", vpiPulldownPrim};
  }
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
  // §37.83: the instance's table of operator attributes.
  const RtlirNodeAttributes* attrs = nullptr;
  // §37.42: the instance's module, whose declarations a terminal's call finds
  // its callee among.
  const RtlirModule* mod = nullptr;
};

// The expression object of the terminal `terminal` written at `site`, a call
// in it standing in the instance (§37.42).
VpiObject* TerminalExpression(const Expr* terminal, const PrimSite& site,
                              SimContext& ctx, const VpiAttachBuild& build) {
  static const std::vector<std::string_view> kNoGenBlocks;
  const VpiCallStand kStand{site.instance, site.mod};
  return VpiGenBlockExpression(
      terminal,
      {site.objects, site.prefix, kNoGenBlocks, nullptr, site.attrs, &kStand},
      ctx, build);
}

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
    // §37.46: the term is a driver or a load of the net it connects.
    VpiHangOnNetsNamed(term, terminals[i]);
    prim->children.push_back(term);
  }
  prim->size = inputs;
  return prim;
}

// §37.3.4: the delay expression vpiDelay reaches from a primitive whose
// instantiation at `site` wrote `delays`; null where it wrote none.
VpiObject* PrimitiveDelayExpression(const std::vector<const Expr*>& delays,
                                    const PrimSite& site, SimContext& ctx,
                                    const VpiAttachBuild& build) {
  return VpiSourceDelayExpression(delays, VpiFlatName(site.prefix, ""), ctx,
                                  build.alloc);
}

// The same for a gate or switch instantiation `item`.
VpiObject* GateDelayExpression(const ModuleItem& item, const PrimSite& site,
                               SimContext& ctx, const VpiAttachBuild& build) {
  return PrimitiveDelayExpression(
      {item.gate_delay, item.gate_delay_fall, item.gate_delay_decay}, site, ctx,
      build);
}

// §37.35 with §28.16: the delays the gate or switch instantiation `item` at
// `site` was written with, a rise, a fall and a turn-off, as vpi_get_delays
// reads them.
std::vector<VpiDelayInfo> GateDelays(const ModuleItem& item,
                                     const PrimSite& site, SimContext& ctx) {
  return VpiWrittenDelays(
      {item.gate_delay, item.gate_delay_fall, item.gate_delay_decay}, true,
      VpiFlatName(site.prefix, ""), ctx);
}

// The expressions `item`'s terminals are written as at `site`.
std::vector<VpiObject*> TerminalObjects(const ModuleItem& item,
                                        const PrimSite& site, SimContext& ctx,
                                        const VpiAttachBuild& build) {
  std::vector<VpiObject*> terminals;
  terminals.reserve(item.gate_terminals.size());
  for (const Expr* terminal : item.gate_terminals) {
    terminals.push_back(TerminalExpression(terminal, site, ctx, build));
  }
  return terminals;
}

// What one instance array of primitives is made of: the instantiation `item`
// writing its range and terminals, the shape its elements share, the kind of
// array, the delay each element is instantiated with, the udp defn a udp
// array's elements reach, null for a gate or switch array, and the delays each
// element reports through vpi_get_delays.
struct PrimArraySpec {
  const ModuleItem& item;
  PrimShape shape;
  int kind;
  VpiObject* delay;
  VpiObject* udp_defn = nullptr;
  std::vector<VpiDelayInfo> delays = {};
};

// §37.11 with §28.3.6: the instance array `spec` describes at `site`, a gate,
// switch or udp array over a primitive per element, each named by its index
// and reaching it (§37.35 detail 4), and the array reaching the delay every
// element is instantiated with.
void MakePrimitiveArray(const PrimArraySpec& spec, const PrimSite& site,
                        SimContext& ctx, const VpiAttachBuild& build) {
  const ModuleItem& item = spec.item;
  const PackedRange kRange = [&] {
    InstancePrefixOverride scope(ctx.InstancePrefixOverride(),
                                 site.prefix.empty() ? "" : site.prefix + ".");
    return VpiEvaluatedRange(item.inst_range_left, item.inst_range_right, ctx);
  }();
  const int64_t kLength = kRange.HighIndex() - kRange.LowIndex() + 1;
  VpiObject* array = VpiMakeInstanceArray(site.instance, spec.kind,
                                          item.gate_inst_name, kRange, build);
  array->delay_expr = spec.delay;
  // §28.3.6 with §37.35: each element's prim terms reach what the elaborator
  // connected that element to, the terminals InstanceArrayElementTerminals
  // gives it under the module's parameter values: a terminal as wide as the
  // array its bit -- a vector's net bit or var bit, a bit of a packed
  // subarray or of an unpacked element, a literal's bit as a constant -- and
  // any other whole. Shared out by the model's objects instead, a terminal
  // whose object held no bit objects, `p[1]` or `mem[1]`, stood whole for
  // every element.
  const ScopeMap kScope = DpiParameterScope(*site.mod);
  const GateArraySite kTerms{site.mod, kScope, build.arena};
  for (int64_t index = kRange.LowIndex(); index <= kRange.HighIndex();
       ++index) {
    std::vector<VpiObject*> terminals;
    for (const Expr* terminal : InstanceArrayElementTerminals(
             item.gate_terminals, kTerms, static_cast<uint32_t>(kLength),
             static_cast<uint32_t>(kRange.OffsetOf(index)))) {
      terminals.push_back(TerminalExpression(terminal, site, ctx, build));
    }
    const std::string kName =
        std::string(item.gate_inst_name) + "[" + std::to_string(index) + "]";
    VpiObject* prim =
        MakePrimitiveObject(spec.shape, kName, terminals, site.instance, build);
    prim->delay_expr = spec.delay;
    prim->delays = spec.delays;
    prim->udp_defn = spec.udp_defn;
    // §37.35 detail 2 and §38.32: the name a put to a sequential udp element
    // finds the running instance under, as for a udp standing alone
    // (MakeUdpObject), and a vpi_put_delays files its new delays below.
    prim->run_key = VpiFlatName(site.prefix, kName);
    VpiRecordWrittenLocation(prim, item.loc, ctx);
    VpiAddArrayElement(array, prim, index, build);
  }
}

// §29.8 with §37.35: the shape of an instance of the UDP `decl`, of the type
// its state makes it.
PrimShape UdpShape(const UdpDecl& decl) {
  return {decl.name, decl.is_sequential ? vpiSeqPrim : vpiCombPrim, vpiUdp};
}

// §29.8 with §37.3.4: the delay a UDP instantiation `inst` was written with at
// `site`, the two §29.8 admits.
VpiObject* UdpDelayExpression(const RtlirUdpInst& inst, const PrimSite& site,
                              SimContext& ctx, const VpiAttachBuild& build) {
  return PrimitiveDelayExpression({inst.delay, inst.delay_fall}, site, ctx,
                                  build);
}

// §37.35 with §29.8: the same delays as vpi_get_delays reads them, a rise and
// a fall, a UDP having no z to turn off to.
std::vector<VpiDelayInfo> UdpDelays(const RtlirUdpInst& inst,
                                    const PrimSite& site, SimContext& ctx) {
  return VpiWrittenDelays({inst.delay, inst.delay_fall, nullptr}, false,
                          VpiFlatName(site.prefix, ""), ctx);
}

// §29.8 with §37.35: the udp the instantiation `inst` of a UDP makes at `site`,
// its output terminal first and its inputs after it as §29.8 writes them, and
// reaching the udp defn `defn` of the UDP it instantiates. Answers the object
// made.
VpiObject* MakeUdpObject(const RtlirUdpInst& inst, const PrimSite& site,
                         VpiObject* defn, SimContext& ctx,
                         const VpiAttachBuild& build) {
  std::vector<VpiObject*> terminals;
  terminals.reserve(inst.inputs.size() + 1);
  terminals.push_back(TerminalExpression(inst.output, site, ctx, build));
  for (const Expr* input : inst.inputs) {
    terminals.push_back(TerminalExpression(input, site, ctx, build));
  }
  VpiObject* udp = MakePrimitiveObject(UdpShape(*inst.decl), inst.name,
                                       terminals, site.instance, build);
  udp->udp_defn = defn;
  udp->delay_expr = UdpDelayExpression(inst, site, ctx, build);
  udp->delays = UdpDelays(inst, site, ctx);
  // §37.35 detail 2: the name a put to a sequential UDP finds the running
  // instance under.
  udp->run_key = VpiFlatName(site.prefix, inst.name);
  // §37.3.3: where the instantiation was written.
  VpiRecordWrittenLocation(udp, inst.loc, ctx);
  return udp;
}

// §29.8 with §37.11: the udps the instance at `site` instantiates. An
// instantiation writing a range, which the elaborator expanded into an
// instance per element, is one udp array over them (§28.3.6), made once.
void MakeInstanceUdps(const RtlirModule& mod, const PrimSite& site,
                      const VpiUdpDefnOf& udp_defn_of, SimContext& ctx,
                      const VpiAttachBuild& build) {
  std::unordered_set<const ModuleItem*> arrays;
  for (const RtlirUdpInst& inst : mod.udp_insts) {
    VpiObject* defn = udp_defn_of(inst.decl);
    if (inst.source_item->inst_range_left != nullptr) {
      if (arrays.insert(inst.source_item).second) {
        MakePrimitiveArray(
            {*inst.source_item, UdpShape(*inst.decl), vpiUdpArray,
             UdpDelayExpression(inst, site, ctx, build), defn,
             UdpDelays(inst, site, ctx)},
            site, ctx, build);
      }
      continue;
    }
    VpiObject* udp = MakeUdpObject(inst, site, defn, ctx, build);
    VpiAttachAttributes(udp, VpiNodeAttributes(&mod, inst.source_item), false,
                        ctx, build);
  }
}

}  // namespace

void AttachPrimitives(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiUdpDefnOf& udp_defn_of, SimContext& ctx,
                      const VpiAttachBuild& build) {
  // §37.35: an instance reaches the gates, switches and udps it instantiates,
  // each with its terminals and, §37.3.4, the delay it was written with.
  // RtlirModule::gate_insts kept each gate and switch instantiation and
  // udp_insts each UDP one, and no pass read either, so vpiPrimitive reached
  // nothing for any design.
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string& prefix,
          VpiObject* instance) {
        for (const ModuleItem* item : mod->gate_insts) {
          const PrimSite kSite{instance, prefix, objects, &mod->node_attrs,
                               mod};
          // §28.3.6: an instantiation declaring a range is an
          // instance array.
          if (item->inst_range_left != nullptr) {
            const PrimShape kShape = ShapeOf(item->gate_kind);
            MakePrimitiveArray(
                {*item, kShape,
                 kShape.type == vpiSwitch ? vpiSwitchArray : vpiGateArray,
                 GateDelayExpression(*item, kSite, ctx, build), nullptr,
                 GateDelays(*item, kSite, ctx)},
                kSite, ctx, build);
            continue;
          }
          VpiObject* prim = MakePrimitiveObject(
              ShapeOf(item->gate_kind), item->gate_inst_name,
              TerminalObjects(*item, kSite, ctx, build), instance, build);
          prim->delay_expr = GateDelayExpression(*item, kSite, ctx, build);
          prim->delays = GateDelays(*item, kSite, ctx);
          // §38.32: the name the run keys the instance under, which a
          // vpi_put_delays files its new delays below.
          prim->run_key = VpiFlatName(prefix, item->gate_inst_name);
          // §37.3.3: where the instantiation was written.
          VpiRecordWrittenLocation(prim, item->loc, ctx);
          // §37.83: the attributes it is written with.
          VpiAttachAttributes(prim, VpiNodeAttributes(mod, item), false, ctx,
                              build);
        }
        MakeInstanceUdps(*mod,
                         {instance, prefix, objects, &mod->node_attrs, mod},
                         udp_defn_of, ctx, build);
      });
}

}  // namespace delta
