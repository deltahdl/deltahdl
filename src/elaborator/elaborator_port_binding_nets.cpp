#include <cstddef>
#include <format>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_bind_scope.h"
#include "elaborator/elaborator_gen_block_interfaces.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_port_binding_internal.h"
#include "elaborator/net_data_type.h"
#include "elaborator/property_instance.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

static bool NameIsInterface(std::string_view name,
                            const CompilationUnit* unit) {
  for (const auto* i : unit->interfaces) {
    if (i->name == name) return true;
  }
  return false;
}

static bool PortAlreadyFlagged(const RtlirModuleInst& inst,
                               std::string_view name) {
  if (!inst.resolved) return false;
  for (const auto& rp : inst.resolved->ports) {
    if (rp.name == name && rp.is_interface_port) return true;
  }
  return false;
}

static void CheckOneNamedInterfacePort(const PortBindCtx& ctx,
                                       const PortDecl& port,
                                       const RtlirModuleInst& inst) {
  const Expr* conn = nullptr;
  for (const auto& binding : inst.port_bindings) {
    if (binding.port_name == port.name) {
      conn = binding.connection;
      break;
    }
  }
  std::string_view conn_name = ConnectedInterfaceName(conn);
  if (conn_name.empty()) return;

  bool found = false;
  std::string_view conn_ifc_type =
      ResolveConnectedInterfaceType(ctx, conn_name, found);
  if (found && !conn_ifc_type.empty() &&
      conn_ifc_type != port.data_type.type_name) {
    ctx.diag.Error(
        ctx.item->loc,
        std::format("interface port '{}' requires interface type '{}' "
                    "but is connected to instance of type '{}'",
                    port.name, port.data_type.type_name, conn_ifc_type),
        Subclause("23.3.3.4"));
  }
}

static void CheckNamedInterfaceTypePorts(const PortBindCtx& ctx,
                                         const ModuleDecl* child_decl,
                                         const RtlirModuleInst& inst,
                                         const CompilationUnit* unit) {
  if (!child_decl) return;

  for (const auto& port : child_decl->ports) {
    if (port.data_type.kind != DataTypeKind::kNamed) continue;
    if (!NameIsInterface(port.data_type.type_name, unit)) continue;
    if (PortAlreadyFlagged(inst, port.name)) continue;
    CheckOneNamedInterfacePort(ctx, port, inst);
  }
}

static std::string_view SignalNettypeName(std::string_view name,
                                          const RtlirModule* mod) {
  for (const auto& n : mod->nets) {
    if (n.name == name) {
      return n.is_user_nettype ? n.nettype_name : std::string_view{};
    }
  }
  return {};
}

static std::string_view InternalPortNettype(
    const ModuleDecl* child_decl, std::string_view port_name,
    const std::unordered_map<std::string_view, std::string_view>&
        nettype_canonical) {
  for (const auto& port : child_decl->ports) {
    if (port.name != port_name) continue;
    if (port.data_type.kind != DataTypeKind::kNamed) break;
    auto it = nettype_canonical.find(NamedTypeKey(port.data_type));
    if (it != nettype_canonical.end()) return it->first;
    break;
  }
  return {};
}

static const RtlirPort* FindPortByName(
    const std::vector<RtlirPort>& child_ports, std::string_view name) {
  for (const auto& p : child_ports) {
    if (p.name == name) return &p;
  }
  return nullptr;
}

static std::string OneSidedInoutMessage(const RtlirPortBinding& binding,
                                        std::string_view nettype,
                                        bool nettype_is_internal) {
  if (nettype_is_internal) {
    return std::format(
        "inout port '{}' of user-defined nettype '{}' is "
        "connected to no net of that nettype; a port with a "
        "nettype on one side only shall be an input or an "
        "output",
        binding.port_name, nettype);
  }
  return std::format(
      "user-defined nettype signal '{}' cannot connect to "
      "inout port '{}'",
      binding.connection->text, binding.port_name);
}

static void CheckOneSidedNettypePort(const PortBindCtx& ctx,
                                     const RtlirModuleInst& inst,
                                     const RtlirPortBinding& binding,
                                     std::string_view nettype,
                                     bool nettype_is_internal) {
  if (binding.direction == Direction::kInout) {
    ctx.diag.Error(ctx.item->loc,
                   OneSidedInoutMessage(binding, nettype, nettype_is_internal),
                   Subclause("23.3.3"));
    return;
  }
  const RtlirPort* port =
      FindPortByName(inst.resolved->ports, binding.port_name);
  if (port == nullptr ||
      !PortAndSignalDiffer(*port, binding.connection->text, ctx.parent_mod)) {
    return;
  }
  ctx.diag.Error(ctx.item->loc,
                 std::format("port '{}' joins user-defined nettype '{}' to a "
                             "connection whose data type does not match it",
                             binding.port_name, nettype),
                 Subclause("23.3.3"));
}

static void CheckMatchingNettypePorts(
    const PortBindCtx& ctx, const ModuleDecl* child_decl,
    const RtlirModuleInst& inst,
    const std::unordered_map<std::string_view, std::string_view>&
        nettype_canonical) {
  if (!child_decl || !inst.resolved) return;

  for (const auto& binding : inst.port_bindings) {
    const Expr* conn = binding.connection;
    if (!conn || conn->kind != ExprKind::kIdentifier) continue;

    std::string_view internal_nettype =
        InternalPortNettype(child_decl, binding.port_name, nettype_canonical);
    std::string_view external_nettype =
        SignalNettypeName(conn->text, ctx.parent_mod);
    if (internal_nettype.empty() != external_nettype.empty()) {
      bool internal = !internal_nettype.empty();
      CheckOneSidedNettypePort(ctx, inst, binding,
                               internal ? internal_nettype : external_nettype,
                               internal);
      continue;
    }
    if (internal_nettype.empty()) continue;

    if (!NettypesMatch(internal_nettype, external_nettype, nettype_canonical)) {
      ctx.diag.Error(
          ctx.item->loc,
          std::format("port '{}' connects user-defined nettype '{}' on the "
                      "instance side to non-matching nettype '{}'; both sides "
                      "shall be the same nettype",
                      binding.port_name, internal_nettype, external_nettype),
          Subclause("23.3.3"));
    }
  }
}

static void RetypeNet(RtlirModule* parent_mod, std::string_view name,
                      NetType type) {
  for (auto& net : parent_mod->nets) {
    if (net.name == name) {
      net.net_type = type;
      return;
    }
  }
}

static void CollapseOneDissimilarNetType(
    RtlirModule* parent_mod, const std::vector<RtlirPort>& child_ports,
    const RtlirPortBinding& binding) {
  const Expr* conn = binding.connection;
  if (!conn || conn->kind != ExprKind::kIdentifier) return;

  const RtlirPort* port = FindPortByName(child_ports, binding.port_name);
  if (!port) return;

  NetType internal = port->net_type;
  NetType external = FindSignalNetType(conn->text, parent_mod);
  if (internal == NetType::kNone || external == NetType::kNone) return;
  if (internal == external) return;
  if (!DissimilarNetResultIsInternal(internal, external)) return;

  RetypeNet(parent_mod, conn->text, internal);
}

static void CollapseDissimilarNetTypes(RtlirModule* parent_mod,
                                       const RtlirModuleInst& inst) {
  if (!parent_mod || !inst.resolved) return;
  for (const auto& binding : inst.port_bindings)
    CollapseOneDissimilarNetType(parent_mod, inst.resolved->ports, binding);
}

static void CollapseOneInterconnectNetType(
    RtlirModule* parent_mod, const std::vector<RtlirPort>& child_ports,
    const RtlirPortBinding& binding,
    const std::unordered_set<std::string_view>& interconnect_names) {
  const Expr* conn = binding.connection;
  if (!conn || conn->kind != ExprKind::kIdentifier) return;
  if (interconnect_names.count(conn->text) == 0) return;

  const RtlirPort* port = FindPortByName(child_ports, binding.port_name);
  if (!port || port->is_interconnect) return;

  NetType internal = port->net_type;
  if (internal == NetType::kNone) return;

  for (auto& net : parent_mod->nets) {
    if (net.name != conn->text) continue;
    net.net_type = MergedInterconnectNetType(net.net_type, internal);
    break;
  }
}

static void CollapseInterconnectNetTypes(
    RtlirModule* parent_mod, const RtlirModuleInst& inst,
    const std::unordered_set<std::string_view>& interconnect_names) {
  if (!parent_mod || !inst.resolved) return;
  for (const auto& binding : inst.port_bindings)
    CollapseOneInterconnectNetType(parent_mod, inst.resolved->ports, binding,
                                   interconnect_names);
}

static void ReportRepeatedPortConnections(const ModuleItem* item,
                                          DiagEngine& diag) {
  std::unordered_set<std::string_view> seen;
  std::unordered_set<std::string_view> reported;
  for (const auto& [name, conn] : item->inst_ports) {
    if (name.empty() || seen.insert(name).second) continue;
    if (!reported.insert(name).second) continue;
    diag.Error(item->loc,
               std::format("port '{}' of module '{}' is connected more than "
                           "once",
                           name, item->inst_module),
               Subclause("23.3.2.2"));
  }
}

void Elaborator::BindPorts(RtlirModuleInst& inst, const ModuleItem* item,
                           RtlirModule* parent_mod,
                           const ModuleDecl* child_decl) {
  if (!inst.resolved) return;
  ReportRepeatedPortConnections(item, diag_);
  const auto& child_ports = inst.resolved->ports;

  const PortBindScope kScope{
      inst, item, parent_mod,
      inst.resolved->unconnected_drive != NetType::kWire,
      !item->inst_ports.empty() && item->inst_ports[0].first.empty()};
  inst.ports_by_name = !kScope.is_ordered;

  for (size_t i = 0; i < item->inst_ports.size(); ++i) {
    if (!BindExplicitPort(kScope, i)) break;
  }

  if (item->inst_wildcard) {
    BindWildcardPorts(kScope);
  } else {
    BindTrailingInputPorts(kScope);
  }
  if (inst.resolved->is_checker && !item->inst_in_procedure) {
    FillInferredCheckerDefaults(
        inst,
        {DefaultClockingEvent(parent_mod), parent_mod->default_disable_iff},
        arena_);
  }

  const std::function<const ModuleDecl*(std::string_view)> kFindModule =
      [&](std::string_view name) { return FindModuleInScope(name); };
  const ScopeMap kParams = BuildParamScope(parent_mod);
  const InterfaceActualScope kActualScope{module_decl_path_.back(),
                                          top_decls_,
                                          kFindModule,
                                          interface_inst_types_,
                                          kParams,
                                          arena_,
                                          diag_,
                                          item->loc};
  ResolveGenBlockInterfaceActuals(inst, kActualScope);
  ResolveInstancePathActuals(inst, kActualScope);
  const PortBindCtx kPortCtx{
      diag_,      item,       parent_mod,          nettype_net_names_,
      var_types_, net_names_, interconnect_names_, interface_inst_types_};
  CheckRefPortsConnected(diag_, child_ports, inst, item);
  CheckInterfacePortsConnected(kPortCtx, child_ports, inst);
  ValidateGenericPortModportAccess(child_decl, inst);
  CheckNamedInterfaceTypePorts(kPortCtx, child_decl, inst, unit_);
  CheckMatchingNettypePorts(kPortCtx, child_decl, inst, nettype_canonical_);

  CollapseDissimilarNetTypes(parent_mod, inst);

  CollapseInterconnectNetTypes(parent_mod, inst, interconnect_names_);
}

}  // namespace delta
