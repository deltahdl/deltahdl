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
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

namespace {

uint32_t FindSignalWidth(std::string_view name, const RtlirModule* mod) {
  for (const auto& v : mod->variables) {
    if (v.name == name) return v.width;
  }
  for (const auto& n : mod->nets) {
    if (n.name == name) return n.width;
  }
  for (const auto& p : mod->ports) {
    if (p.name == name) return p.width;
  }
  return 0;
}
NetType FindSignalNetType(std::string_view name, const RtlirModule* mod) {
  for (const auto& n : mod->nets) {
    if (n.name == name) return n.net_type;
  }
  return NetType::kNone;
}
DataTypeKind NormalizeForCompatibility(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kWire:
    case DataTypeKind::kTri:
    case DataTypeKind::kWand:
    case DataTypeKind::kTriand:
    case DataTypeKind::kWor:
    case DataTypeKind::kTrior:
    case DataTypeKind::kTri0:
    case DataTypeKind::kTri1:
    case DataTypeKind::kTrireg:
    case DataTypeKind::kSupply0:
    case DataTypeKind::kSupply1:
    case DataTypeKind::kUwire:
      return DataTypeKind::kLogic;
    default:
      return kind;
  }
}
int NetTypeGroup(NetType t) {
  switch (t) {
    case NetType::kWire:
    case NetType::kTri:
      return 0;
    case NetType::kWand:
    case NetType::kTriand:
      return 1;
    case NetType::kWor:
    case NetType::kTrior:
      return 2;
    case NetType::kTrireg:
      return 3;
    case NetType::kTri0:
      return 4;
    case NetType::kTri1:
      return 5;
    case NetType::kUwire:
      return 6;
    case NetType::kSupply0:
      return 7;
    case NetType::kSupply1:
      return 8;
    default:
      return -1;
  }
}
bool DissimilarNetTypeRequiresWarning(NetType internal, NetType external) {
  static constexpr bool kWarnTable[9][9] = {
      {false, false, false, false, false, false, false, false, false},
      {false, false, true, true, true, true, true, false, false},
      {false, true, false, true, true, true, true, false, false},
      {false, true, true, false, false, false, true, false, false},
      {false, true, true, false, false, true, true, false, false},
      {false, true, true, false, true, false, true, false, false},
      {false, true, true, true, true, true, false, false, false},
      {false, false, false, false, false, false, false, false, true},
      {false, false, false, false, false, false, false, true, false},
  };
  int ig = NetTypeGroup(internal);
  int eg = NetTypeGroup(external);
  if (ig < 0 || eg < 0) return false;
  return kWarnTable[ig][eg];
}
NetType PortNetType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kWire:
      return NetType::kWire;
    case DataTypeKind::kTri:
      return NetType::kTri;
    case DataTypeKind::kWand:
      return NetType::kWand;
    case DataTypeKind::kTriand:
      return NetType::kTriand;
    case DataTypeKind::kWor:
      return NetType::kWor;
    case DataTypeKind::kTrior:
      return NetType::kTrior;
    case DataTypeKind::kTri0:
      return NetType::kTri0;
    case DataTypeKind::kTri1:
      return NetType::kTri1;
    case DataTypeKind::kTrireg:
      return NetType::kTrireg;
    case DataTypeKind::kSupply0:
      return NetType::kSupply0;
    case DataTypeKind::kSupply1:
      return NetType::kSupply1;
    case DataTypeKind::kUwire:
      return NetType::kUwire;
    default:
      return NetType::kNone;
  }
}
Expr* MakePullExprIn(Arena& arena, NetType drive) {
  auto* expr = arena.Create<Expr>();
  expr->kind = ExprKind::kIntegerLiteral;
  expr->int_val = (drive == NetType::kTri1) ? 1 : 0;
  return expr;
}
Expr* MakeHighZExprIn(Arena& arena) {
  auto* expr = arena.Create<Expr>();
  expr->kind = ExprKind::kUnbasedUnsizedLiteral;
  expr->text = "'z";
  return expr;
}
// Identifier reference expression naming `name`, for synthesized connections.
Expr* MakeIdentExprIn(Arena& arena, std::string_view name) {
  auto* expr = arena.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->text = name;
  return expr;
}
// Synthesized connection for an unconnected input: pull, else high-Z net, else
// null.
Expr* DefaultInputConnection(Arena& arena, const RtlirPort& port, bool has_pull,
                             NetType drive) {
  if (has_pull) return MakePullExprIn(arena, drive);
  if (!port.is_var && PortNetType(port.type_kind) != NetType::kNone) {
    return MakeHighZExprIn(arena);
  }
  return nullptr;
}
// True when `port_name` already appears among the explicit port connections.
bool PortExplicitlyConnected(
    const std::vector<std::pair<std::string_view, Expr*>>& inst_ports,
    std::string_view port_name) {
  for (const auto& [pname, _] : inst_ports)
    if (pname == port_name) return true;
  return false;
}

// §23.3.3 per-instance port-binding context shared by the connection checks.
struct PortBindCtx {
  DiagEngine& diag;
  const ModuleItem* item;
  const RtlirModule* parent_mod;
  const std::unordered_set<std::string_view>& nettype_net_names;
  const std::unordered_map<std::string_view, DataTypeKind>& var_types;
  const std::unordered_set<std::string_view>& net_names;
  const std::unordered_set<std::string_view>& interconnect_names;
  const std::unordered_map<std::string_view, std::string_view>&
      interface_inst_types;
};

// §23.3.x one identifier connection bound to a port, for the legality rules.
struct IdentConnection {
  Direction direction;
  std::string_view conn_name;
  std::string_view port_name;
  bool is_var;
};
// §23.3.2.3 implicit .name form: connected signal shall match width/net type.
void CheckImplicitNamedPortNetTypes(const PortBindCtx& ctx,
                                    std::string_view port_name,
                                    const Expr* conn_expr,
                                    const RtlirPort* port_it) {
  uint32_t sig_width = FindSignalWidth(conn_expr->text, ctx.parent_mod);
  if (sig_width != 0 && sig_width != port_it->width) {
    ctx.diag.Error(ctx.item->loc,
                   std::format("implicit named port connection '.{}' requires "
                               "equivalent data types (port width {}, "
                               "signal width {})",
                               port_name, port_it->width, sig_width));
  }
  NetType pnet = PortNetType(port_it->type_kind);
  if (pnet == NetType::kNone) return;
  NetType snet = FindSignalNetType(conn_expr->text, ctx.parent_mod);
  // 23.3.2.3: the implicit .name form errors exactly where the explicit named
  // connection would merely warn (23.3.3.7); equivalent net types are exempt.
  if (snet != NetType::kNone && snet != NetType::kInterconnect &&
      !port_it->is_interconnect &&
      DissimilarNetTypeRequiresWarning(pnet, snet)) {
    ctx.diag.Error(ctx.item->loc,
                   std::format("implicit named port connection '.{}' between "
                               "dissimilar net types",
                               port_name));
  }
}
// §23.3.3.7: explicit identifier connection between dissimilar net types warns.
void CheckExplicitNamedPortNetTypes(const PortBindCtx& ctx, bool is_implicit,
                                    const Expr* conn_expr,
                                    const RtlirPort* port_it,
                                    std::string_view binding_port_name) {
  if (is_implicit || !conn_expr || conn_expr->kind != ExprKind::kIdentifier) {
    return;
  }
  NetType pnet = PortNetType(port_it->type_kind);
  if (pnet == NetType::kNone) return;
  NetType snet = FindSignalNetType(conn_expr->text, ctx.parent_mod);
  if (snet != NetType::kNone && snet != pnet &&
      DissimilarNetTypeRequiresWarning(pnet, snet)) {
    ctx.diag.Warning(ctx.item->loc,
                     std::format("port '{}' connected between dissimilar "
                                 "net types",
                                 binding_port_name));
  }
}
// §23.3.3.x: every ref port shall be connected; errors on each left
// unconnected.
void CheckRefPortsConnected(DiagEngine& diag,
                            const std::vector<RtlirPort>& child_ports,
                            const RtlirModuleInst& inst,
                            const ModuleItem* item) {
  for (const auto& port : child_ports) {
    if (port.direction != Direction::kRef) continue;
    bool connected = false;
    for (const auto& binding : inst.port_bindings) {
      if (binding.port_name == port.name && binding.connection) {
        connected = true;
        break;
      }
    }
    if (!connected) {
      diag.Error(item->loc,
                 std::format("ref port '{}' of module '{}' cannot be "
                             "left unconnected",
                             port.name, inst.module_name));
    }
  }
}
// Interface type named by `conn_name`; `found` reports whether it is known.
std::string_view ResolveConnectedInterfaceType(const PortBindCtx& ctx,
                                               std::string_view conn_name,
                                               bool& found) {
  auto iit = ctx.interface_inst_types.find(conn_name);
  if (iit != ctx.interface_inst_types.end()) {
    found = true;
    return iit->second;
  }
  for (const auto& pp : ctx.parent_mod->ports) {
    if (pp.name == conn_name && pp.is_interface_port) {
      found = true;
      return pp.interface_type_name;
    }
  }
  found = false;
  return {};
}
// Validates one interface port binding (connected, type-matched interface).
void CheckOneInterfacePortConnected(const PortBindCtx& ctx,
                                    const RtlirPort& port,
                                    const RtlirModuleInst& inst) {
  Expr* conn = nullptr;
  for (const auto& binding : inst.port_bindings) {
    if (binding.port_name == port.name) {
      conn = binding.connection;
      break;
    }
  }
  if (!conn) {
    ctx.diag.Error(ctx.item->loc,
                   std::format("interface port '{}' of module '{}' cannot be "
                               "left unconnected",
                               port.name, inst.module_name));
    return;
  }
  std::string_view conn_name;
  if (conn->kind == ExprKind::kIdentifier) {
    conn_name = conn->text;
  } else if (conn->kind == ExprKind::kMemberAccess && conn->lhs &&
             conn->lhs->kind == ExprKind::kIdentifier && conn->rhs &&
             conn->rhs->kind == ExprKind::kIdentifier) {
    conn_name = conn->lhs->text;
  }
  bool found = false;
  std::string_view conn_ifc_type =
      conn_name.empty() ? std::string_view{}
                        : ResolveConnectedInterfaceType(ctx, conn_name, found);
  if (conn_name.empty() || !found) {
    ctx.diag.Error(ctx.item->loc,
                   std::format("interface port '{}' must be connected to an "
                               "interface instance or interface port",
                               port.name));
    return;
  }
  if (!port.interface_type_name.empty() && !conn_ifc_type.empty() &&
      port.interface_type_name != conn_ifc_type) {
    ctx.diag.Error(
        ctx.item->loc,
        std::format("interface port '{}' requires interface type '{}' "
                    "but is connected to instance of type '{}'",
                    port.name, port.interface_type_name, conn_ifc_type));
  }
}
void CheckInterfacePortsConnected(const PortBindCtx& ctx,
                                  const std::vector<RtlirPort>& child_ports,
                                  const RtlirModuleInst& inst) {
  for (const auto& port : child_ports) {
    if (!port.is_interface_port) continue;
    CheckOneInterfacePortConnected(ctx, port, inst);
  }
}
// §23.3.3.2: true when `conn_name` is an interconnect net or interconnect port.
bool ConnectsToInterconnect(
    std::string_view conn_name,
    const std::unordered_set<std::string_view>& interconnect_names,
    const RtlirModule* parent_mod) {
  if (interconnect_names.count(conn_name)) return true;
  for (const auto& p : parent_mod->ports)
    if (p.name == conn_name && p.is_interconnect) return true;
  return false;
}
// §23.3.x directional legality (four rules) for an identifier connection.
void CheckDirectionalConnectionLegality(const PortBindCtx& ctx,
                                        const IdentConnection& conn) {
  DiagEngine& diag = ctx.diag;
  SourceLoc loc = ctx.item->loc;
  auto cn = conn.conn_name;
  auto pn = conn.port_name;
  if (conn.direction == Direction::kInout && ctx.nettype_net_names.count(cn)) {
    diag.Error(loc, std::format("user-defined nettype signal '{}' cannot "
                                "connect to inout port '{}'",
                                cn, pn));
  }
  if (conn.direction == Direction::kInout && ctx.var_types.count(cn) &&
      ctx.net_names.count(cn) == 0) {
    diag.Error(loc, std::format("variable '{}' cannot be connected to "
                                "inout port '{}'",
                                cn, pn));
  }
  if (conn.direction == Direction::kRef && ctx.net_names.count(cn)) {
    diag.Error(loc, std::format("net '{}' cannot be connected to ref port "
                                "'{}'; ref port requires a variable",
                                cn, pn));
  }
  if (conn.is_var &&
      ConnectsToInterconnect(cn, ctx.interconnect_names, ctx.parent_mod)) {
    diag.Error(loc, std::format("port variable '{}' cannot be connected to "
                                "interconnect '{}'",
                                pn, cn));
  }
}
// §23.3.3 assignment-compat + directional legality for an identifier
// connection.
void CheckExplicitIdentifierConnection(const PortBindCtx& ctx,
                                       const Expr* conn_expr,
                                       const RtlirPort& port,
                                       std::string_view binding_port_name) {
  DataTypeKind port_kind = NormalizeForCompatibility(port.type_kind);
  if (port_kind != DataTypeKind::kImplicit) {
    DataTypeKind sig_kind = DataTypeKind::kImplicit;
    auto vt = ctx.var_types.find(conn_expr->text);
    if (vt != ctx.var_types.end()) {
      sig_kind = NormalizeForCompatibility(vt->second);
    } else if (ctx.net_names.count(conn_expr->text)) {
      sig_kind = DataTypeKind::kLogic;
    }
    if (sig_kind != DataTypeKind::kImplicit) {
      DataType port_dt{};
      port_dt.kind = port_kind;
      DataType sig_dt{};
      sig_dt.kind = sig_kind;
      if (!IsAssignmentCompatible(sig_dt, port_dt)) {
        ctx.diag.Error(ctx.item->loc,
                       std::format("port connection type is not assignment "
                                   "compatible with port '{}'",
                                   binding_port_name));
      }
    }
  }
  CheckDirectionalConnectionLegality(
      ctx, IdentConnection{port.direction, conn_expr->text, binding_port_name,
                           port.is_var});
}
// True when a replication operator appears anywhere in `e`.
bool ConnectionHasReplication(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kReplicate) return true;
  if (e->kind == ExprKind::kConcatenation) {
    for (const auto* el : e->elements)
      if (ConnectionHasReplication(el)) return true;
  }
  return false;
}
// §23.3.3 extra state the completion loops need beyond PortBindCtx.
struct PortCompletionCtx {
  Arena& arena;
  std::unordered_map<std::string_view, SourceLoc>& output_port_targets;
  bool has_pull;
  NetType drive;
};
// §23.3.2.3 implicit named connection: named signal shall be declared in scope.
void CheckImplicitNamedDeclared(const PortBindCtx& ctx,
                                std::string_view port_name,
                                const Expr* conn_expr) {
  if (IsNameDeclared(conn_expr->text, ctx.parent_mod)) return;
  ctx.diag.Error(
      ctx.item->loc,
      std::format("implicit named port connection '.{}' requires signal '{}' "
                  "to be declared in the instantiating scope",
                  port_name, conn_expr->text));
}
// §23.3.x resolves a connection's child port, fills binding fields, runs
// checks.
std::vector<RtlirPort>::const_iterator ResolveBindingPort(
    const PortBindCtx& ctx, const std::vector<RtlirPort>& child_ports,
    const RtlirModuleInst& inst, RtlirPortBinding& binding, size_t i,
    std::string_view port_name, const Expr* conn_expr, bool is_implicit,
    bool is_ordered, bool& overflow) {
  overflow = false;
  auto it = child_ports.end();
  if (is_ordered) {
    if (i < child_ports.size()) {
      it = child_ports.begin() + static_cast<ptrdiff_t>(i);
      binding.port_name = it->name;
    } else {
      ctx.diag.Warning(
          ctx.item->loc,
          std::format("too many ordered port connections for module '{}'"
                      " (expected {}, got {})",
                      inst.module_name, child_ports.size(),
                      ctx.item->inst_ports.size()));
      overflow = true;
      return child_ports.end();
    }
  } else {
    binding.port_name = port_name;
    it = std::find_if(child_ports.begin(), child_ports.end(),
                      [&](const RtlirPort& p) { return p.name == port_name; });
  }
  if (it == child_ports.end()) {
    ctx.diag.Warning(ctx.item->loc,
                     std::format("port '{}' not found on module '{}'",
                                 port_name, inst.module_name));
    binding.direction = Direction::kInput;
    binding.width = 1;
    return it;
  }
  binding.direction = it->direction;
  binding.width = it->width;
  if (is_implicit && conn_expr &&
      IsNameDeclared(conn_expr->text, ctx.parent_mod)) {
    CheckImplicitNamedPortNetTypes(ctx, port_name, conn_expr, &*it);
  }
  CheckExplicitNamedPortNetTypes(ctx, is_implicit, conn_expr, &*it,
                                 binding.port_name);
  return it;
}
// §23.3.3 syntactic legality: no replication in output/inout, no
// assign-pattern.
void CheckConnectionExprLegality(const PortBindCtx& ctx, const Expr* conn_expr,
                                 Direction direction) {
  if (!conn_expr) return;
  if (direction != Direction::kInput && ConnectionHasReplication(conn_expr)) {
    ctx.diag.Error(conn_expr->range.start,
                   "replication shall not appear in an output or inout "
                   "port connection");
  }
  bool is_pattern = conn_expr->kind == ExprKind::kAssignmentPattern ||
                    (conn_expr->kind == ExprKind::kCast && conn_expr->lhs &&
                     conn_expr->lhs->kind == ExprKind::kAssignmentPattern);
  if (is_pattern) {
    ctx.diag.Error(conn_expr->range.start,
                   "assignment pattern expression shall not be used in a "
                   "port expression");
  }
}
// §23.3.3.2: records a non-input port's driven name; errors on a second driver.
void RegisterOutputTarget(const PortBindCtx& ctx, PortCompletionCtx& comp,
                          Direction direction, std::string_view name) {
  if (direction == Direction::kInput || ctx.net_names.count(name) != 0) return;
  if (!comp.output_port_targets.emplace(name, ctx.item->loc).second) {
    ctx.diag.Error(
        ctx.item->loc,
        std::format("variable '{}' driven by multiple outputs", name));
  }
}
// §25.5: header and instance modport selections shall name the same modport.
void CheckModportHeaderMatch(const PortBindCtx& ctx,
                             const ModuleDecl* child_decl,
                             const RtlirPort& port, const Expr* conn_expr,
                             std::string_view binding_port_name) {
  if (!port.is_interface_port || !conn_expr ||
      conn_expr->kind != ExprKind::kMemberAccess || !conn_expr->lhs ||
      conn_expr->lhs->kind != ExprKind::kIdentifier || !conn_expr->rhs ||
      conn_expr->rhs->kind != ExprKind::kIdentifier) {
    return;
  }
  std::string_view header_modport;
  if (child_decl) {
    for (const auto& p : child_decl->ports) {
      if (p.name == binding_port_name) {
        header_modport = p.data_type.modport_name;
        break;
      }
    }
  }
  auto connection_modport = conn_expr->rhs->text;
  if (!header_modport.empty() && !connection_modport.empty() &&
      header_modport != connection_modport) {
    ctx.diag.Error(
        ctx.item->loc,
        std::format("interface port '{}' selects modport '{}' in the module "
                    "header but '{}' in the instance connection; both shall "
                    "name the same modport",
                    binding_port_name, header_modport, connection_modport));
  }
}
// §23.3.2.4 default for an unconnected port: declared default, else input
// synth.
Expr* DefaultUnconnectedConnection(const PortCompletionCtx& comp,
                                   const RtlirPort& port) {
  if (port.default_value) return port.default_value;
  if (port.direction == Direction::kInput) {
    return DefaultInputConnection(comp.arena, port, comp.has_pull, comp.drive);
  }
  return nullptr;
}
// §23.3.2.4 synthesizes a wildcard (.*) binding for one unconnected child port.
void BindOneWildcardPort(const PortBindCtx& ctx, PortCompletionCtx& comp,
                         const RtlirModuleInst& inst, const RtlirPort& port,
                         RtlirModuleInst& out_inst) {
  RtlirPortBinding binding;
  binding.port_name = port.name;
  binding.direction = port.direction;
  binding.width = port.width;
  if (port.is_interface_port) {
    if (port.interface_type_name.empty()) {
      ctx.diag.Error(ctx.item->loc,
                     std::format("implicit .* port connection cannot reference "
                                 "generic interface port '{}' of module '{}'",
                                 port.name, inst.module_name));
    } else if (ctx.interface_inst_types.count(port.name)) {
      binding.connection = MakeIdentExprIn(comp.arena, port.name);
    }
  } else if (IsNameDeclared(port.name, ctx.parent_mod)) {
    uint32_t sig_width = FindSignalWidth(port.name, ctx.parent_mod);
    if (sig_width != 0 && sig_width != port.width) {
      ctx.diag.Error(ctx.item->loc,
                     std::format("implicit .* port connection '.{}' requires "
                                 "equivalent data types (port width {}, "
                                 "signal width {})",
                                 port.name, port.width, sig_width));
    }
    NetType pnet = PortNetType(port.type_kind);
    if (pnet != NetType::kNone) {
      NetType snet = FindSignalNetType(port.name, ctx.parent_mod);
      if (snet != NetType::kNone && snet != pnet &&
          snet != NetType::kInterconnect && !port.is_interconnect) {
        ctx.diag.Error(ctx.item->loc,
                       std::format("implicit .* port connection '.{}' between "
                                   "dissimilar net types",
                                   port.name));
      }
    }
    CheckDirectionalConnectionLegality(
        ctx,
        IdentConnection{port.direction, port.name, port.name, port.is_var});
    binding.connection = MakeIdentExprIn(comp.arena, port.name);
    RegisterOutputTarget(ctx, comp, binding.direction, port.name);
  } else {
    binding.connection = DefaultUnconnectedConnection(comp, port);
  }
  if (binding.connection) {
    out_inst.port_bindings.push_back(binding);
  }
}

// §23.3.2.4 completes unconnected ports (wildcard binds all; else trailing in).
void CompleteUnconnectedPorts(const PortBindCtx& ctx, PortCompletionCtx& comp,
                              const RtlirModuleInst& inst,
                              const std::vector<RtlirPort>& child_ports,
                              bool is_ordered, RtlirModuleInst& out_inst) {
  if (ctx.item->inst_wildcard) {
    for (const auto& port : child_ports) {
      if (PortExplicitlyConnected(ctx.item->inst_ports, port.name)) continue;
      BindOneWildcardPort(ctx, comp, inst, port, out_inst);
    }
    return;
  }
  size_t first_unconnected = is_ordered ? ctx.item->inst_ports.size() : 0;
  for (size_t i = first_unconnected; i < child_ports.size(); ++i) {
    const auto& port = child_ports[i];
    if (port.direction != Direction::kInput) continue;
    if (!is_ordered &&
        PortExplicitlyConnected(ctx.item->inst_ports, port.name)) {
      continue;
    }
    RtlirPortBinding binding;
    binding.port_name = port.name;
    binding.direction = port.direction;
    binding.width = port.width;
    binding.connection = DefaultUnconnectedConnection(comp, port);
    if (binding.connection) {
      out_inst.port_bindings.push_back(binding);
    }
  }
}

}  // namespace

Expr* Elaborator::MakePullExpr(NetType drive) {
  return MakePullExprIn(arena_, drive);
}
Expr* Elaborator::MakeHighZExpr() { return MakeHighZExprIn(arena_); }

void Elaborator::BindPorts(RtlirModuleInst& inst, const ModuleItem* item,
                           RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;
  const bool kHasPull = unit_->unconnected_drive != NetType::kWire;

  const bool kIsOrdered =
      !item->inst_ports.empty() && item->inst_ports[0].first.empty();

  // §23.3.3 shared port-binding context for every connection check below.
  const PortBindCtx kPortCtx{
      diag_,      item,       parent_mod,          nettype_net_names_,
      var_types_, net_names_, interconnect_names_, interface_inst_types_};

  const ModuleDecl* child_decl = FindModule(inst.module_name);
  PortCompletionCtx kCompCtx{arena_, output_port_targets_, kHasPull,
                             unit_->unconnected_drive};

  for (size_t i = 0; i < item->inst_ports.size(); ++i) {
    auto& [port_name, conn_expr] = item->inst_ports[i];
    const bool kIsImplicit =
        i < item->inst_ports_implicit.size() && item->inst_ports_implicit[i];

    if (conn_expr && conn_expr->kind == ExprKind::kIdentifier) {
      if (kIsImplicit) {
        CheckImplicitNamedDeclared(kPortCtx, port_name, conn_expr);
      } else if (!interface_inst_types_.count(conn_expr->text)) {
        MaybeCreateImplicitNet(conn_expr->text, item->loc, parent_mod);
      }
    }
    RtlirPortBinding binding;
    binding.connection = conn_expr;
    bool overflow = false;
    auto it =
        ResolveBindingPort(kPortCtx, child_ports, inst, binding, i, port_name,
                           conn_expr, kIsImplicit, kIsOrdered, overflow);
    if (overflow) break;
    if (conn_expr && conn_expr->kind == ExprKind::kIdentifier &&
        it != child_ports.end() && !it->is_interface_port) {
      CheckExplicitIdentifierConnection(kPortCtx, conn_expr, *it,
                                        binding.port_name);
    }
    CheckConnectionExprLegality(kPortCtx, conn_expr, binding.direction);
    if (conn_expr && conn_expr->kind == ExprKind::kIdentifier) {
      RegisterOutputTarget(kPortCtx, kCompCtx, binding.direction,
                           conn_expr->text);
    }
    if (kIsOrdered && !binding.connection &&
        binding.direction == Direction::kInput && it != child_ports.end() &&
        it->default_value) {
      binding.connection = it->default_value;
    }
    if (kHasPull && !binding.connection &&
        binding.direction == Direction::kInput) {
      binding.connection = MakePullExpr(unit_->unconnected_drive);
    }
    if (!binding.connection && binding.direction == Direction::kInput &&
        it != child_ports.end() && !it->is_var &&
        PortNetType(it->type_kind) != NetType::kNone) {
      binding.connection = MakeHighZExpr();
    }
    if (it != child_ports.end()) {
      CheckModportHeaderMatch(kPortCtx, child_decl, *it, conn_expr,
                              binding.port_name);
    }
    inst.port_bindings.push_back(binding);
  }

  CompleteUnconnectedPorts(kPortCtx, kCompCtx, inst, child_ports, kIsOrdered,
                           inst);

  CheckRefPortsConnected(diag_, child_ports, inst, item);
  CheckInterfacePortsConnected(kPortCtx, child_ports, inst);
}

void Elaborator::CheckPortCoercion(const RtlirModuleInst& inst, SourceLoc loc) {
  if (!inst.resolved) return;

  std::unordered_set<std::string_view> child_assign_targets;
  for (const auto& ca : inst.resolved->assigns) {
    if (ca.lhs && ca.lhs->kind == ExprKind::kIdentifier)
      child_assign_targets.insert(ca.lhs->text);
  }

  for (const auto& binding : inst.port_bindings) {
    if (binding.direction == Direction::kInput &&
        child_assign_targets.count(binding.port_name)) {
      diag_.Warning(loc,
                    std::format("port '{}' is declared as input but is driven "
                                "inside module '{}'",
                                binding.port_name, inst.module_name));
    }

    if (binding.direction == Direction::kOutput && binding.connection &&
        binding.connection->kind == ExprKind::kIdentifier &&
        cont_assign_targets_.count(binding.connection->text)) {
      diag_.Warning(
          loc, std::format("port '{}' is declared as output but its connection "
                           "'{}' is also driven externally",
                           binding.port_name, binding.connection->text));
    }
  }
}

// Looks up a child port by name; returns nullptr when no port matches.
static const RtlirPort* FindChildPortByName(
    const std::vector<RtlirPort>& child_ports, std::string_view name) {
  auto port_it =
      std::find_if(child_ports.begin(), child_ports.end(),
                   [&](const RtlirPort& p) { return p.name == name; });
  if (port_it == child_ports.end()) return nullptr;
  return &*port_it;
}

// Resolves the child port a binding connects to; nullptr when none/unconnected.
static const RtlirPort* FindBoundChildPort(
    const std::vector<RtlirPort>& child_ports,
    const RtlirPortBinding& binding) {
  if (!binding.connection) return nullptr;
  return FindChildPortByName(child_ports, binding.port_name);
}

void Elaborator::CheckUwirePortMerge(const RtlirModuleInst& inst,
                                     const ModuleItem* item,
                                     RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    const RtlirPort* port_it = FindBoundChildPort(child_ports, binding);
    if (!port_it) continue;

    NetType internal_net = PortNetType(port_it->type_kind);
    bool internal_is_uwire = (internal_net == NetType::kUwire);

    bool external_is_net = false;
    bool external_is_uwire = false;
    if (binding.connection->kind == ExprKind::kIdentifier) {
      NetType ext = FindSignalNetType(binding.connection->text, parent_mod);
      external_is_net = (ext != NetType::kNone);
      external_is_uwire = (ext == NetType::kUwire);
    }

    if (!internal_is_uwire && !external_is_uwire) continue;

    bool merged = (internal_net != NetType::kNone) && external_is_net;
    if (!merged) {
      diag_.Warning(
          item->loc,
          std::format("uwire net on port '{}' of instance '{}' is not "
                      "merged into a single net",
                      binding.port_name, inst.inst_name));
    }
  }
}

void Elaborator::CheckInterconnectPortMerge(const RtlirModuleInst& inst,
                                            const ModuleItem* item,
                                            RtlirModule*) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    const RtlirPort* port_it = FindBoundChildPort(child_ports, binding);
    if (!port_it) continue;

    bool internal_is_interconnect = port_it->is_interconnect;

    bool external_is_interconnect = false;
    if (binding.connection->kind == ExprKind::kIdentifier) {
      external_is_interconnect =
          interconnect_names_.count(binding.connection->text) != 0;
    }

    if (internal_is_interconnect && external_is_interconnect) {
      diag_.Error(
          item->loc,
          std::format("simulated net for port '{}' of instance '{}' has "
                      "interconnect type at end of elaboration",
                      binding.port_name, inst.inst_name));
    }
  }
}

void Elaborator::ResolveInterconnectPrimitiveTerminals(
    const std::vector<Expr*>& terminals, RtlirModule* mod) {
  for (const auto* term : terminals) {
    if (!term || term->kind != ExprKind::kIdentifier) continue;
    if (interconnect_names_.count(term->text) == 0) continue;
    auto scoped = ScopedName(term->text);
    for (auto& net : mod->nets) {
      if (net.name == scoped && net.net_type == NetType::kInterconnect) {
        net.net_type = NetType::kWire;
        break;
      }
    }
    interconnect_names_.erase(term->text);
  }
}

// Validates one unpacked-array port binding (matching dim count and sizes).
static void CheckUnpackedArrayPortBinding(
    DiagEngine& diag, const ModuleItem* item, const RtlirPortBinding& binding,
    const RtlirPort* port_it,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info) {
  if (!binding.connection ||
      binding.connection->kind != ExprKind::kIdentifier) {
    diag.Error(item->loc,
               std::format("unpacked array port '{}' requires a matching "
                           "unpacked array connection",
                           binding.port_name));
    return;
  }

  auto it = var_array_info.find(binding.connection->text);
  if (it == var_array_info.end()) {
    diag.Error(item->loc,
               std::format("unpacked array port '{}' requires a matching "
                           "unpacked array connection",
                           binding.port_name));
    return;
  }

  const auto& conn_info = it->second;
  if (conn_info.num_unpacked_dims != port_it->num_unpacked_dims) {
    diag.Error(
        item->loc,
        std::format("unpacked array port '{}' has {} unpacked dimension(s) "
                    "but connection has {}",
                    binding.port_name, port_it->num_unpacked_dims,
                    conn_info.num_unpacked_dims));
    return;
  }

  for (uint32_t d = 0; d < port_it->num_unpacked_dims; ++d) {
    if (d < port_it->unpacked_dim_sizes.size() &&
        d < conn_info.dim_sizes.size() &&
        port_it->unpacked_dim_sizes[d] != conn_info.dim_sizes[d]) {
      diag.Error(
          item->loc,
          std::format("unpacked array port '{}' dimension {} has size {} "
                      "but connection has size {}",
                      binding.port_name, d, port_it->unpacked_dim_sizes[d],
                      conn_info.dim_sizes[d]));
      break;
    }
  }
}

void Elaborator::ValidateUnpackedArrayPorts(const RtlirModuleInst& inst,
                                            const ModuleItem* item,
                                            RtlirModule*) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    const RtlirPort* port_it =
        FindChildPortByName(child_ports, binding.port_name);
    if (!port_it) continue;
    if (port_it->num_unpacked_dims == 0) continue;
    CheckUnpackedArrayPortBinding(diag_, item, binding, port_it,
                                  var_array_info_);
  }
}

// The connecting signal's unpacked-array shape: dim count and known dim sizes.
struct ConnArrayShape {
  uint32_t num_dims;
  const std::vector<uint32_t>* dim_sizes;
};

// Validates an unpacked-array connection against an instance-array port.
static void CheckInstanceArrayUnpackedConn(
    const PortBindCtx& ctx, const RtlirPortBinding& binding,
    const RtlirPort* port_it, const ConnArrayShape& conn,
    const std::vector<uint32_t>& inst_dim_sizes) {
  uint32_t expected_dims =
      static_cast<uint32_t>(inst_dim_sizes.size()) + port_it->num_unpacked_dims;
  if (conn.num_dims != expected_dims) {
    ctx.diag.Error(
        ctx.item->loc,
        std::format("unpacked array connection to port '{}' has {} "
                    "dimension(s) but expected {}",
                    binding.port_name, conn.num_dims, expected_dims));
    return;
  }
  if (!conn.dim_sizes) return;
  for (size_t d = 0; d < inst_dim_sizes.size(); ++d) {
    if (d < conn.dim_sizes->size() &&
        (*conn.dim_sizes)[d] != inst_dim_sizes[d]) {
      ctx.diag.Error(ctx.item->loc,
                     std::format("unpacked array connection to port '{}' "
                                 "dimension {} has size {} but instance array "
                                 "has size {}",
                                 binding.port_name, d, (*conn.dim_sizes)[d],
                                 inst_dim_sizes[d]));
      return;
    }
  }
  for (uint32_t d = 0; d < port_it->num_unpacked_dims; ++d) {
    uint32_t ci = static_cast<uint32_t>(inst_dim_sizes.size()) + d;
    if (ci < conn.dim_sizes->size() && d < port_it->unpacked_dim_sizes.size() &&
        (*conn.dim_sizes)[ci] != port_it->unpacked_dim_sizes[d]) {
      ctx.diag.Error(ctx.item->loc,
                     std::format("unpacked array connection to port '{}' "
                                 "port dimension {} has size {} but port "
                                 "expects {}",
                                 binding.port_name, d, (*conn.dim_sizes)[ci],
                                 port_it->unpacked_dim_sizes[d]));
      return;
    }
  }
}

// Validates one binding vs an instance-array port (unpacked shape or width).
static void ValidateOneInstanceArrayPort(
    const PortBindCtx& ctx, const RtlirPortBinding& binding,
    const RtlirPort* port_it,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const std::vector<uint32_t>& inst_dim_sizes, uint32_t total_instances) {
  bool conn_is_unpacked = false;
  ConnArrayShape shape{0, nullptr};
  uint32_t conn_width = 0;
  if (binding.connection->kind == ExprKind::kIdentifier) {
    auto it = var_array_info.find(binding.connection->text);
    if (it != var_array_info.end()) {
      conn_is_unpacked = true;
      shape =
          ConnArrayShape{it->second.num_unpacked_dims, &it->second.dim_sizes};
    }
    conn_width = FindSignalWidth(binding.connection->text, ctx.parent_mod);
  }
  if (conn_is_unpacked) {
    CheckInstanceArrayUnpackedConn(ctx, binding, port_it, shape,
                                   inst_dim_sizes);
    return;
  }
  if (conn_width == 0 || conn_width == port_it->width) return;
  uint32_t expected_width = port_it->width * total_instances;
  if (conn_width != expected_width) {
    ctx.diag.Error(
        ctx.item->loc,
        std::format("packed array connection to port '{}' has width {} "
                    "but expected {} ({} instances * port width {})",
                    binding.port_name, conn_width, expected_width,
                    total_instances, port_it->width));
  }
}

void Elaborator::ValidateInstanceArrayPorts(
    const RtlirModuleInst& inst, const ModuleItem* item,
    RtlirModule* parent_mod, const std::vector<uint32_t>& inst_dim_sizes,
    uint32_t total_instances) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;
  const PortBindCtx kPortCtx{
      diag_,      item,       parent_mod,          nettype_net_names_,
      var_types_, net_names_, interconnect_names_, interface_inst_types_};
  for (const auto& binding : inst.port_bindings) {
    const RtlirPort* port_it = FindBoundChildPort(child_ports, binding);
    if (!port_it) continue;
    ValidateOneInstanceArrayPort(kPortCtx, binding, port_it, var_array_info_,
                                 inst_dim_sizes, total_instances);
  }
}

}  // namespace delta
