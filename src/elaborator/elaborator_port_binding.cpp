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

namespace {

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

// Synthesized connection for an unconnected input port: a pull expression when
// an unconnected drive is set, else high-Z for a net-typed (non-var) port, else
// nullptr. Shared by the wildcard and trailing-input completion loops.
Expr* DefaultInputConnection(Arena& arena, const RtlirPort& port, bool has_pull,
                             NetType drive) {
  if (has_pull) return MakePullExprIn(arena, drive);
  if (!port.is_var && PortNetType(port.type_kind) != NetType::kNone) {
    return MakeHighZExprIn(arena);
  }
  return nullptr;
}

// True when `port_name` already appears among the instance's explicit port
// connections; lets the completion loops skip already-bound ports.
bool PortExplicitlyConnected(
    const std::vector<std::pair<std::string_view, Expr*>>& inst_ports,
    std::string_view port_name) {
  for (const auto& [pname, _] : inst_ports)
    if (pname == port_name) return true;
  return false;
}

}  // namespace

Expr* Elaborator::MakePullExpr(NetType drive) {
  return MakePullExprIn(arena_, drive);
}

Expr* Elaborator::MakeHighZExpr() { return MakeHighZExprIn(arena_); }

namespace {

// §23.3.x one identifier connection bound to a port, for the legality rules.
struct IdentConnection {
  Direction direction;
  std::string_view conn_name;
  std::string_view port_name;
  bool is_var;
};

// §23.3.2.3 implicit .name form: the connected signal shall have an equivalent
// width and (for a net port) a non-dissimilar net type; both mismatches error.
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

// §23.3.3.7: an explicit named or ordered connection between dissimilar net
// types warns. Applies only to the non-implicit identifier connection form.
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

// §23.3.3.x: every ref port of the instantiated module shall have a connected
// binding; emits an error for each that is left unconnected.
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

// Validates one interface port binding: it must be connected, name an interface
// instance or interface port, and match the port's declared interface type.
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

// §23.3.3.2: true when `conn_name` resolves to an interconnect signal of the
// instantiating module (a local interconnect net or interconnect port).
bool ConnectsToInterconnect(
    std::string_view conn_name,
    const std::unordered_set<std::string_view>& interconnect_names,
    const RtlirModule* parent_mod) {
  if (interconnect_names.count(conn_name)) return true;
  for (const auto& p : parent_mod->ports)
    if (p.name == conn_name && p.is_interconnect) return true;
  return false;
}

// §23.3.x directional connection legality for an identifier connection bound to
// a port; the four independent rules match the original inline sequence.
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

// §23.3.3 assignment-compatibility check for an identifier connection to a
// non-interface port, followed by the shared directional legality checks.
void CheckExplicitIdentifierConnection(const PortBindCtx& ctx,
                                       const Expr* conn_expr,
                                       const RtlirPort& port,
                                       std::string_view binding_port_name) {
  DataTypeKind port_kind = NormalizeForCompatibility(port.type_kind);
  // §23.3.3.7/§6.6.7: a user-defined nettype net carries its own net-type
  // semantics; its compatibility with a port is governed by the dissimilar
  // net-type rules (which warn for an explicit connection), not by data-type
  // assignment compatibility. Its var_types_ entry is the meaningless kNamed
  // nettype reference, so skip the kind-based check for such a connection.
  if (port_kind != DataTypeKind::kImplicit &&
      ctx.nettype_net_names.count(conn_expr->text) == 0) {
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

}  // namespace

void Elaborator::CheckPortModportConsistency(const PortBindScope& scope,
                                             const RtlirPortBinding& binding,
                                             const Expr* conn_expr,
                                             const RtlirPort* child_port) {
  // §25.5: when a modport is selected in both the module header and the
  // instance connection, both shall name the same modport.
  if (!child_port || !child_port->is_interface_port || !conn_expr ||
      conn_expr->kind != ExprKind::kMemberAccess || !conn_expr->lhs ||
      conn_expr->lhs->kind != ExprKind::kIdentifier || !conn_expr->rhs ||
      conn_expr->rhs->kind != ExprKind::kIdentifier) {
    return;
  }
  std::string_view header_modport;
  if (const auto* child_decl = FindModule(scope.inst.module_name)) {
    for (const auto& p : child_decl->ports) {
      if (p.name == binding.port_name) {
        header_modport = p.data_type.modport_name;
        break;
      }
    }
  }
  auto connection_modport = conn_expr->rhs->text;
  if (!header_modport.empty() && !connection_modport.empty() &&
      header_modport != connection_modport) {
    diag_.Error(
        scope.item->loc,
        std::format("interface port '{}' selects modport '{}' in the module "
                    "header but '{}' in the instance connection; both shall "
                    "name the same modport",
                    binding.port_name, header_modport, connection_modport));
  }
}

void Elaborator::PrepareExplicitConnNet(const PortBindScope& scope,
                                        const ExplicitPortBind& bind) {
  const Expr* conn_expr = bind.conn_expr;
  if (!conn_expr || conn_expr->kind != ExprKind::kIdentifier) return;
  if (bind.is_implicit) {
    if (!IsNameDeclared(conn_expr->text, scope.parent_mod)) {
      diag_.Error(
          scope.item->loc,
          std::format("implicit named port connection '.{}' requires "
                      "signal '{}' to be declared in the instantiating scope",
                      bind.port_name, conn_expr->text));
    }
  } else if (!interface_inst_types_.count(conn_expr->text)) {
    MaybeCreateImplicitNet(conn_expr->text, scope.item->loc, scope.parent_mod);
  }
}

bool Elaborator::ResolveExplicitTarget(const PortBindScope& scope, size_t index,
                                       ExplicitPortBind& bind) {
  RtlirModuleInst& inst = scope.inst;
  const ModuleItem* item = scope.item;
  const auto& child_ports = inst.resolved->ports;
  RtlirPortBinding& binding = bind.binding;

  const PortBindCtx kPortCtx{
      diag_,      item,       scope.parent_mod,    nettype_net_names_,
      var_types_, net_names_, interconnect_names_, interface_inst_types_};

  if (scope.is_ordered) {
    if (index >= child_ports.size()) {
      diag_.Warning(
          item->loc,
          std::format("too many ordered port connections for module '{}'"
                      " (expected {}, got {})",
                      inst.module_name, child_ports.size(),
                      item->inst_ports.size()));
      return false;
    }
    bind.child_port = &child_ports[index];
    binding.port_name = bind.child_port->name;
  } else {
    binding.port_name = bind.port_name;
    auto it = std::find_if(
        child_ports.begin(), child_ports.end(),
        [&](const RtlirPort& p) { return p.name == bind.port_name; });
    bind.child_port = (it == child_ports.end()) ? nullptr : &*it;
  }

  const RtlirPort* port = bind.child_port;
  if (!port) {
    diag_.Warning(item->loc, std::format("port '{}' not found on module '{}'",
                                         bind.port_name, inst.module_name));
    binding.direction = Direction::kInput;
    binding.width = 1;
    return true;
  }

  binding.direction = port->direction;
  binding.width = port->width;
  if (bind.is_implicit && bind.conn_expr &&
      IsNameDeclared(bind.conn_expr->text, scope.parent_mod)) {
    CheckImplicitNamedPortNetTypes(kPortCtx, bind.port_name, bind.conn_expr,
                                   port);
  }
  CheckExplicitNamedPortNetTypes(kPortCtx, bind.is_implicit, bind.conn_expr,
                                 port, binding.port_name);
  return true;
}

void Elaborator::CheckExplicitConnLegality(const PortBindScope& scope,
                                           const ExplicitPortBind& bind) {
  const Expr* conn_expr = bind.conn_expr;
  const RtlirPortBinding& binding = bind.binding;
  const RtlirPort* port = bind.child_port;

  const PortBindCtx kPortCtx{
      diag_,      scope.item, scope.parent_mod,    nettype_net_names_,
      var_types_, net_names_, interconnect_names_, interface_inst_types_};

  if (conn_expr && conn_expr->kind == ExprKind::kIdentifier && port &&
      !port->is_interface_port) {
    CheckExplicitIdentifierConnection(kPortCtx, conn_expr, *port,
                                      binding.port_name);
  }

  if (conn_expr && binding.direction != Direction::kInput &&
      ConnectionHasReplication(conn_expr)) {
    diag_.Error(conn_expr->range.start,
                "replication shall not appear in an output or inout "
                "port connection");
  }

  if (conn_expr) {
    bool is_pattern = conn_expr->kind == ExprKind::kAssignmentPattern ||
                      (conn_expr->kind == ExprKind::kCast && conn_expr->lhs &&
                       conn_expr->lhs->kind == ExprKind::kAssignmentPattern);
    if (is_pattern) {
      diag_.Error(conn_expr->range.start,
                  "assignment pattern expression shall not be used in a "
                  "port expression");
    }
  }

  if (conn_expr && conn_expr->kind == ExprKind::kIdentifier &&
      binding.direction != Direction::kInput &&
      net_names_.count(conn_expr->text) == 0) {
    auto name = conn_expr->text;
    if (!output_port_targets_.emplace(name, scope.item->loc).second) {
      diag_.Error(
          scope.item->loc,
          std::format("variable '{}' driven by multiple outputs", name));
    }
  }
}

void Elaborator::SynthesizeExplicitDefault(const PortBindScope& scope,
                                           ExplicitPortBind& bind) {
  RtlirPortBinding& binding = bind.binding;
  const RtlirPort* port = bind.child_port;
  if (binding.direction != Direction::kInput) return;

  if (scope.is_ordered && !binding.connection && port && port->default_value) {
    binding.connection = port->default_value;
  }
  if (scope.has_pull && !binding.connection) {
    binding.connection = MakePullExpr(unit_->unconnected_drive);
  }
  if (!binding.connection && port && !port->is_var &&
      PortNetType(port->type_kind) != NetType::kNone) {
    binding.connection = MakeHighZExpr();
  }
}

bool Elaborator::BindExplicitPort(const PortBindScope& scope, size_t index) {
  const ModuleItem* item = scope.item;
  auto& [port_name, conn_expr] = item->inst_ports[index];

  RtlirPortBinding binding;
  binding.connection = conn_expr;
  ExplicitPortBind bind{binding, conn_expr, port_name, nullptr,
                        index < item->inst_ports_implicit.size() &&
                            item->inst_ports_implicit[index]};

  PrepareExplicitConnNet(scope, bind);
  if (!ResolveExplicitTarget(scope, index, bind)) return false;
  CheckExplicitConnLegality(scope, bind);
  SynthesizeExplicitDefault(scope, bind);
  CheckPortModportConsistency(scope, binding, conn_expr, bind.child_port);

  scope.inst.port_bindings.push_back(binding);
  return true;
}

void Elaborator::BindWildcardDeclaredPort(const PortBindScope& scope,
                                          const RtlirPort& port,
                                          RtlirPortBinding& binding) {
  const ModuleItem* item = scope.item;
  RtlirModule* parent_mod = scope.parent_mod;

  const PortBindCtx kPortCtx{
      diag_,      item,       parent_mod,          nettype_net_names_,
      var_types_, net_names_, interconnect_names_, interface_inst_types_};

  uint32_t sig_width = FindSignalWidth(port.name, parent_mod);
  if (sig_width != 0 && sig_width != port.width) {
    diag_.Error(item->loc,
                std::format("implicit .* port connection '.{}' requires "
                            "equivalent data types (port width {}, "
                            "signal width {})",
                            port.name, port.width, sig_width));
  }
  NetType pnet = PortNetType(port.type_kind);
  if (pnet != NetType::kNone) {
    NetType snet = FindSignalNetType(port.name, parent_mod);
    if (snet != NetType::kNone && snet != pnet &&
        snet != NetType::kInterconnect && !port.is_interconnect) {
      diag_.Error(item->loc,
                  std::format("implicit .* port connection '.{}' between "
                              "dissimilar net types",
                              port.name));
    }
  }
  CheckDirectionalConnectionLegality(
      kPortCtx,
      IdentConnection{port.direction, port.name, port.name, port.is_var});
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->text = port.name;
  binding.connection = expr;
  if (binding.direction != Direction::kInput &&
      net_names_.count(port.name) == 0 &&
      !output_port_targets_.emplace(port.name, item->loc).second) {
    diag_.Error(
        item->loc,
        std::format("variable '{}' driven by multiple outputs", port.name));
  }
}

void Elaborator::BindOneWildcardPort(const PortBindScope& scope,
                                     const RtlirPort& port) {
  RtlirModuleInst& inst = scope.inst;
  const ModuleItem* item = scope.item;
  RtlirModule* parent_mod = scope.parent_mod;

  RtlirPortBinding binding;
  binding.port_name = port.name;
  binding.direction = port.direction;
  binding.width = port.width;

  if (port.is_interface_port) {
    if (port.interface_type_name.empty()) {
      diag_.Error(item->loc,
                  std::format("implicit .* port connection cannot reference "
                              "generic interface port '{}' of module '{}'",
                              port.name, inst.module_name));
    } else if (interface_inst_types_.count(port.name)) {
      auto* expr = arena_.Create<Expr>();
      expr->kind = ExprKind::kIdentifier;
      expr->text = port.name;
      binding.connection = expr;
    }
  } else if (IsNameDeclared(port.name, parent_mod)) {
    BindWildcardDeclaredPort(scope, port, binding);
  } else if (port.default_value) {
    binding.connection = port.default_value;
  } else if (port.direction == Direction::kInput) {
    binding.connection = DefaultInputConnection(arena_, port, scope.has_pull,
                                                unit_->unconnected_drive);
  }

  if (binding.connection) {
    inst.port_bindings.push_back(binding);
  }
}

void Elaborator::BindWildcardPorts(const PortBindScope& scope) {
  const auto& child_ports = scope.inst.resolved->ports;
  for (const auto& port : child_ports) {
    if (PortExplicitlyConnected(scope.item->inst_ports, port.name)) continue;
    BindOneWildcardPort(scope, port);
  }
}

void Elaborator::BindTrailingInputPorts(const PortBindScope& scope) {
  RtlirModuleInst& inst = scope.inst;
  const ModuleItem* item = scope.item;
  const auto& child_ports = inst.resolved->ports;

  size_t first_unconnected = scope.is_ordered ? item->inst_ports.size() : 0;
  for (size_t i = first_unconnected; i < child_ports.size(); ++i) {
    const auto& port = child_ports[i];
    if (port.direction != Direction::kInput) continue;

    if (!scope.is_ordered &&
        PortExplicitlyConnected(item->inst_ports, port.name)) {
      continue;
    }

    RtlirPortBinding binding;
    binding.port_name = port.name;
    binding.direction = port.direction;
    binding.width = port.width;

    if (port.default_value) {
      binding.connection = port.default_value;
    } else {
      binding.connection = DefaultInputConnection(arena_, port, scope.has_pull,
                                                  unit_->unconnected_drive);
    }

    if (binding.connection) {
      inst.port_bindings.push_back(binding);
    }
  }
}

void Elaborator::BindPorts(RtlirModuleInst& inst, const ModuleItem* item,
                           RtlirModule* parent_mod) {
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
}

}  // namespace delta
