#include <algorithm>
#include <cstdint>
#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_port_binding_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

// Returns the identifier naming the connected interface instance/port for a
// binding connection, or an empty view for a non-identifier expression.
static std::string_view ConnectionInterfaceName(const Expr* conn) {
  if (!conn) return {};
  if (conn->kind == ExprKind::kIdentifier) return conn->text;
  if (conn->kind == ExprKind::kMemberAccess && conn->lhs &&
      conn->lhs->kind == ExprKind::kIdentifier) {
    return conn->lhs->text;
  }
  return {};
}

// True when `name` is declared as an interface in the compilation unit.
static bool NameIsInterface(std::string_view name,
                            const CompilationUnit* unit) {
  for (const auto* i : unit->interfaces) {
    if (i->name == name) return true;
  }
  return false;
}

// True when the elaborated module's port of this name already carries the
// interface-port flag, in which case CheckInterfacePortsConnected enforces it
// and re-checking here would duplicate the diagnostic.
static bool PortAlreadyFlagged(const RtlirModuleInst& inst,
                               std::string_view name) {
  if (!inst.resolved) return false;
  for (const auto& rp : inst.resolved->ports) {
    if (rp.name == name && rp.is_interface_port) return true;
  }
  return false;
}

// Errors when one named interface-type port is connected to an interface
// instance of a different type than the port's declared interface type.
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
  std::string_view conn_name = ConnectionInterfaceName(conn);
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
                    port.name, port.data_type.type_name, conn_ifc_type));
  }
}

// §23.3.3.4/§25.3.2: a named interface-type port (`bus_if p`) must connect to
// an interface instance of the identical type. The required type is taken from
// the child declaration, so the rule holds even when the elaborated port's
// is_interface_port flag was not set during nested port elaboration.
static void CheckNamedInterfaceTypePorts(const PortBindCtx& ctx,
                                         const ModuleDecl* child_decl,
                                         const RtlirModuleInst& inst,
                                         const CompilationUnit* unit) {
  if (!child_decl) return;

  for (const auto& port : child_decl->ports) {
    // An interface-type port carries no meaningful direction (the parser may
    // leave the ANSI default in place), so the rule keys off the named type
    // being an interface rather than the direction.
    if (port.data_type.kind != DataTypeKind::kNamed) continue;
    if (!NameIsInterface(port.data_type.type_name, unit)) continue;
    if (PortAlreadyFlagged(inst, port.name)) continue;
    CheckOneNamedInterfacePort(ctx, port, inst);
  }
}

// §23.3.3: the user-defined nettype name of a signal in the instantiating
// module, or an empty view when the signal is not a user-defined nettype net.
static std::string_view SignalNettypeName(std::string_view name,
                                          const RtlirModule* mod) {
  for (const auto& n : mod->nets) {
    if (n.name == name) {
      return n.is_user_nettype ? n.nettype_name : std::string_view{};
    }
  }
  return {};
}

// §23.3.3: when both the internal port and the external connection are
// user-defined nettypes, they shall be of matching nettypes so that the two
// nets can merge into a single simulated net; a mismatch is an error. Matching
// follows §6.22.6 -- a nettype matches itself and any renaming alias of it,
// i.e. their canonical (source) nettype names are equal. Only this both-sided
// case is checked here: a one-sided user-defined nettype is governed by the
// mode/data-type rules elsewhere in §23.3.3, and differences between built-in
// net types by the collapsing rules of §23.3.3.7.
static void CheckMatchingNettypePorts(
    DiagEngine& diag, const ModuleItem* item, const RtlirModule* parent_mod,
    const ModuleDecl* child_decl, const RtlirModuleInst& inst,
    const std::unordered_map<std::string_view, std::string_view>&
        nettype_canonical) {
  if (!child_decl) return;

  auto canonical = [&](std::string_view n) {
    auto it = nettype_canonical.find(n);
    return it != nettype_canonical.end() ? it->second : n;
  };

  for (const auto& binding : inst.port_bindings) {
    const Expr* conn = binding.connection;
    if (!conn || conn->kind != ExprKind::kIdentifier) continue;

    // Internal side: the child port is itself declared with a user-defined
    // nettype (a named type registered in the canonical nettype map).
    std::string_view internal_nettype;
    for (const auto& port : child_decl->ports) {
      if (port.name != binding.port_name) continue;
      if (port.data_type.kind == DataTypeKind::kNamed &&
          nettype_canonical.count(port.data_type.type_name)) {
        internal_nettype = port.data_type.type_name;
      }
      break;
    }
    if (internal_nettype.empty()) continue;

    // External side: the connected signal is a user-defined nettype net.
    std::string_view external_nettype =
        SignalNettypeName(conn->text, parent_mod);
    if (external_nettype.empty()) continue;

    if (internal_nettype != external_nettype &&
        canonical(internal_nettype) != canonical(external_nettype)) {
      diag.Error(
          item->loc,
          std::format("port '{}' connects user-defined nettype '{}' on the "
                      "instance side to non-matching nettype '{}'; both sides "
                      "shall be the same nettype",
                      binding.port_name, internal_nettype, external_nettype));
    }
  }
}

// §23.3.3.7 / Table 23-1: when a port connects two dissimilar built-in net
// types and the internal (module-definition) net dominates, the two nets
// collapse into one simulated net whose type is the dominating (internal) type.
// Materialize that by retyping the instantiation-side net to the internal
// port's net type; when the external net dominates (or neither does) the
// instantiation-side declaration already carries the resulting type, so nothing
// changes. Only bare net-to-net identifier connections collapse; a non-net
// connection, a matching type, or an interconnect net (NetTypeGroup < 0,
// governed by §23.3.3.7.1) is left untouched. Runs after the connectivity
// checks, which read the original types.
static void CollapseDissimilarNetTypes(RtlirModule* parent_mod,
                                       const RtlirModuleInst& inst) {
  if (!parent_mod || !inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    const Expr* conn = binding.connection;
    if (!conn || conn->kind != ExprKind::kIdentifier) continue;

    const RtlirPort* port = nullptr;
    for (const auto& p : child_ports) {
      if (p.name == binding.port_name) {
        port = &p;
        break;
      }
    }
    if (!port) continue;

    NetType internal = PortNetType(port->type_kind);
    NetType external = FindSignalNetType(conn->text, parent_mod);
    if (internal == NetType::kNone || external == NetType::kNone) continue;
    if (internal == external) continue;
    if (!DissimilarNetResultIsInternal(internal, external)) continue;

    for (auto& net : parent_mod->nets) {
      if (net.name == conn->text) {
        net.net_type = internal;
        break;
      }
    }
  }
}

// §23.3.3.7.1: a port connection involving an interconnect net merges the
// interconnect net with the net on the other side of the port into a single
// simulated net. An interconnect net has no net type of its own to contribute,
// so when the other side is a built-in net type the merged net takes that
// type. Materialize that by retyping the interconnect net (identified by the
// declared interconnect names) to the child port's built-in net type. When one
// interconnect net reaches several dissimilar built-in net types through
// separate port connections, the single merged net resolves to the dominating
// type among them, so each newly seen concrete type is folded into the type
// accumulated so far using the same Table 23-1 dominance as the built-in
// collapse. A net that only ever meets interconnect (or variable) ports keeps
// its interconnect type; CheckInterconnectPortMerge then reports it as illegal
// at the end of elaboration. Gating on the interconnect-name set keeps ordinary
// nets (already handled by CollapseDissimilarNetTypes) untouched.
static void CollapseInterconnectNetTypes(
    RtlirModule* parent_mod, const RtlirModuleInst& inst,
    const std::unordered_set<std::string_view>& interconnect_names) {
  if (!parent_mod || !inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    const Expr* conn = binding.connection;
    if (!conn || conn->kind != ExprKind::kIdentifier) continue;
    if (interconnect_names.count(conn->text) == 0) continue;

    const RtlirPort* port = nullptr;
    for (const auto& p : child_ports) {
      if (p.name == binding.port_name) {
        port = &p;
        break;
      }
    }
    if (!port) continue;

    // Only a built-in net type on the child-port side contributes a type; an
    // interconnect or variable port contributes nothing to the merged type.
    NetType internal = PortNetType(port->type_kind);
    if (internal == NetType::kNone) continue;

    for (auto& net : parent_mod->nets) {
      if (net.name != conn->text) continue;
      if (net.net_type == NetType::kInterconnect) {
        net.net_type = internal;
      } else if (net.net_type != internal && NetTypeGroup(net.net_type) >= 0) {
        net.net_type = DissimilarNetResultIsInternal(net.net_type, internal)
                           ? net.net_type
                           : internal;
      }
      break;
    }
  }
}

void Elaborator::BindPorts(RtlirModuleInst& inst, const ModuleItem* item,
                           RtlirModule* parent_mod,
                           const ModuleDecl* child_decl) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  const PortBindScope kScope{
      inst, item, parent_mod, unit_->unconnected_drive != NetType::kWire,
      !item->inst_ports.empty() && item->inst_ports[0].first.empty()};

  for (size_t i = 0; i < item->inst_ports.size(); ++i) {
    if (!BindExplicitPort(kScope, i)) break;
  }

  if (item->inst_wildcard) {
    BindWildcardPorts(kScope);
  } else {
    BindTrailingInputPorts(kScope);
  }

  // §23.3.3 shared port-binding context for the post-bind connectivity checks.
  const PortBindCtx kPortCtx{
      diag_,      item,       parent_mod,          nettype_net_names_,
      var_types_, net_names_, interconnect_names_, interface_inst_types_};
  CheckRefPortsConnected(diag_, child_ports, inst, item);
  CheckInterfacePortsConnected(kPortCtx, child_ports, inst);
  CheckNamedInterfaceTypePorts(kPortCtx, child_decl, inst, unit_);
  CheckMatchingNettypePorts(diag_, item, parent_mod, child_decl, inst,
                            nettype_canonical_);

  // §23.3.3.7: retype the instantiation-side net where the internal port net is
  // the dominating net, so the collapsed simulated net carries the dominating
  // type. The connectivity checks above already ran against the original types.
  CollapseDissimilarNetTypes(parent_mod, inst);

  // §23.3.3.7.1: retype an interconnect net to the built-in net type it merges
  // with through this instance's port connections, so the merged simulated net
  // carries that type. Runs after the built-in collapse and is gated on the
  // declared interconnect names, so it only touches interconnect nets.
  CollapseInterconnectNetTypes(parent_mod, inst, interconnect_names_);
}

}  // namespace delta
