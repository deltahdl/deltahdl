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
    default:
      return {"pulldown", vpiPulldownPrim};
  }
}

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

struct PrimSite {
  VpiObject* instance;
  const std::string& prefix;
  const VpiObjectMap& objects;
  const RtlirNodeAttributes* attrs = nullptr;
  const RtlirModule* mod = nullptr;
};

VpiObject* TerminalExpression(const Expr* terminal, const PrimSite& site,
                              SimContext& ctx, const VpiAttachBuild& build) {
  static const std::vector<std::string_view> kNoGenBlocks;
  const VpiCallStand kStand{site.instance, site.mod};
  return VpiGenBlockExpression(
      terminal,
      {site.objects, site.prefix, kNoGenBlocks, nullptr, site.attrs, &kStand},
      ctx, build);
}

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
    VpiHangOnNetsNamed(term, terminals[i]);
    prim->children.push_back(term);
  }
  prim->size = inputs;
  return prim;
}

VpiObject* PrimitiveDelayExpression(const std::vector<const Expr*>& delays,
                                    const PrimSite& site, SimContext& ctx,
                                    const VpiAttachBuild& build) {
  return VpiSourceDelayExpression(delays, VpiFlatName(site.prefix, ""), ctx,
                                  build.alloc);
}

VpiObject* GateDelayExpression(const ModuleItem& item, const PrimSite& site,
                               SimContext& ctx, const VpiAttachBuild& build) {
  return PrimitiveDelayExpression(
      {item.gate_delay, item.gate_delay_fall, item.gate_delay_decay}, site, ctx,
      build);
}

std::vector<VpiDelayInfo> GateDelays(const ModuleItem& item,
                                     const PrimSite& site, SimContext& ctx) {
  return VpiWrittenDelays(
      {item.gate_delay, item.gate_delay_fall, item.gate_delay_decay}, true,
      VpiFlatName(site.prefix, ""), ctx);
}

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

struct PrimArraySpec {
  const ModuleItem& item;
  PrimShape shape;
  int kind;
  VpiObject* delay;
  VpiObject* udp_defn = nullptr;
  std::vector<VpiDelayInfo> delays = {};
};

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
    prim->run_key = VpiFlatName(site.prefix, kName);
    VpiRecordWrittenLocation(prim, item.loc, ctx);
    VpiAddArrayElement(array, prim, index, build);
  }
}

PrimShape UdpShape(const UdpDecl& decl) {
  return {decl.name, decl.is_sequential ? vpiSeqPrim : vpiCombPrim, vpiUdp};
}

VpiObject* UdpDelayExpression(const RtlirUdpInst& inst, const PrimSite& site,
                              SimContext& ctx, const VpiAttachBuild& build) {
  return PrimitiveDelayExpression({inst.delay, inst.delay_fall}, site, ctx,
                                  build);
}

std::vector<VpiDelayInfo> UdpDelays(const RtlirUdpInst& inst,
                                    const PrimSite& site, SimContext& ctx) {
  return VpiWrittenDelays({inst.delay, inst.delay_fall, nullptr}, false,
                          VpiFlatName(site.prefix, ""), ctx);
}

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
  udp->run_key = VpiFlatName(site.prefix, inst.name);
  VpiRecordWrittenLocation(udp, inst.loc, ctx);
  return udp;
}

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
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string& prefix,
          VpiObject* instance) {
        for (const ModuleItem* item : mod->gate_insts) {
          const PrimSite kSite{instance, prefix, objects, &mod->node_attrs,
                               mod};
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
          prim->run_key = VpiFlatName(prefix, item->gate_inst_name);
          VpiRecordWrittenLocation(prim, item->loc, ctx);
          VpiAttachAttributes(prim, VpiNodeAttributes(mod, item), false, ctx,
                              build);
        }
        MakeInstanceUdps(*mod,
                         {instance, prefix, objects, &mod->node_attrs, mod},
                         udp_defn_of, ctx, build);
      });
}

}  // namespace delta
