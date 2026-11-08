#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_bind_scope.h"
#include "elaborator/elaborator_gen_block_interfaces.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_port_binding_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

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

bool IsNetPort(const RtlirPort& port) {
  return !port.is_var && !port.is_interface_port &&
         port.net_type != NetType::kNone;
}

Expr* DefaultInputConnection(Arena& arena, const RtlirPort& port, bool has_pull,
                             NetType drive) {
  if (has_pull) return MakePullExprIn(arena, drive);
  if (IsNetPort(port)) return MakeHighZExprIn(arena);
  return nullptr;
}

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

struct IdentConnection {
  Direction direction;
  std::string_view conn_name;
  std::string_view port_name;
  bool is_var;
};

void CheckImplicitNamedPortNetTypes(const PortBindCtx& ctx,
                                    std::string_view port_name,
                                    const Expr* conn_expr,
                                    const RtlirPort* port_it) {
  ReportNonEquivalentImplicitConnection(ctx.diag, ctx.item->loc, false,
                                        *port_it, ctx.parent_mod);

  NetType pnet = PortNetType(port_it->type_kind);
  if (pnet == NetType::kNone) return;
  NetType snet = FindSignalNetType(conn_expr->text, ctx.parent_mod);
  bool declared_interconnect =
      ctx.interconnect_names.count(conn_expr->text) != 0 ||
      port_it->is_interconnect;
  if (snet != NetType::kNone && snet != NetType::kInterconnect &&
      !declared_interconnect && DissimilarNetTypeRequiresWarning(pnet, snet)) {
    ctx.diag.Error(ctx.item->loc,
                   std::format("implicit named port connection '.{}' between "
                               "dissimilar net types",
                               port_name),
                   Subclause("23.3.2.3"));
  }
}

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
                                 binding_port_name),
                     Subclause("23.3.3.7"));
  }
}

void CheckOneInterfacePortConnected(const PortBindCtx& ctx,
                                    const RtlirPort& port,
                                    const RtlirModuleInst& inst) {
  Expr* conn = nullptr;
  for (const auto& binding : inst.port_bindings) {
    if (binding.port_name == port.name) {
      if (binding.refused_actual) return;
      conn = binding.connection;
      break;
    }
  }
  if (!conn) {
    if (ctx.item->inst_wildcard && port.interface_type_name.empty()) return;
    ctx.diag.Error(ctx.item->loc,
                   std::format("interface port '{}' of module '{}' cannot be "
                               "left unconnected",
                               port.name, inst.module_name),
                   Subclause("23.3.3.4"));
    return;
  }
  std::string_view conn_name = ConnectedInterfaceName(conn);

  bool found = false;
  std::string_view conn_ifc_type =
      conn_name.empty() ? std::string_view{}
                        : ResolveConnectedInterfaceType(ctx, conn_name, found);
  if (conn_name.empty() || !found) {
    ctx.diag.Error(ctx.item->loc,
                   std::format("interface port '{}' must be connected to an "
                               "interface instance or interface port",
                               port.name),
                   Subclause("23.3.3.4"));
    return;
  }

  if (!port.interface_type_name.empty() && !conn_ifc_type.empty() &&
      port.interface_type_name != conn_ifc_type) {
    ctx.diag.Error(
        ctx.item->loc,
        std::format("interface port '{}' requires interface type '{}' "
                    "but is connected to instance of type '{}'",
                    port.name, port.interface_type_name, conn_ifc_type),
        Subclause("23.3.3.4"));
  }
}

bool ConnectsToInterconnect(
    std::string_view conn_name,
    const std::unordered_set<std::string_view>& interconnect_names,
    const RtlirModule* parent_mod) {
  if (interconnect_names.count(conn_name)) return true;
  for (const auto& p : parent_mod->ports)
    if (p.name == conn_name && p.is_interconnect) return true;
  return false;
}

void CheckDirectionalConnectionLegality(const PortBindCtx& ctx,
                                        const IdentConnection& conn) {
  DiagEngine& diag = ctx.diag;
  SourceLoc loc = ctx.item->loc;
  auto cn = conn.conn_name;
  auto pn = conn.port_name;
  if (conn.direction == Direction::kInout)
    ReportVariableOnInout(ctx, cn, pn, conn.is_var);
  if (conn.direction == Direction::kRef && ctx.net_names.count(cn)) {
    diag.Error(loc,
               std::format("net '{}' cannot be connected to ref port "
                           "'{}'; ref port requires a variable",
                           cn, pn),
               Subclause("23.3.3.2"));
  }
  if (conn.is_var &&
      ConnectsToInterconnect(cn, ctx.interconnect_names, ctx.parent_mod)) {
    diag.Error(loc,
               std::format("port variable '{}' cannot be connected to "
                           "interconnect '{}'",
                           pn, cn),
               Subclause("23.3.3.2"));
  }
}

static DataTypeKind ConnectedSignalKind(const PortBindCtx& ctx,
                                        std::string_view name) {
  auto vt = ctx.var_types.find(name);
  if (vt != ctx.var_types.end()) return NormalizeForCompatibility(vt->second);
  if (ctx.net_names.count(name)) return DataTypeKind::kLogic;
  return DataTypeKind::kImplicit;
}

static void CheckExplicitConnAssignCompatible(
    const PortBindCtx& ctx, const Expr* conn_expr, const RtlirPort& port,
    std::string_view binding_port_name) {
  DataTypeKind port_kind = NormalizeForCompatibility(port.type_kind);
  if (port_kind == DataTypeKind::kImplicit ||
      port_kind == DataTypeKind::kNamed ||
      ctx.nettype_net_names.count(conn_expr->text) != 0 ||
      (ctx.child_is_checker && port_kind == DataTypeKind::kEvent))
    return;
  DataTypeKind sig_kind = ConnectedSignalKind(ctx, conn_expr->text);
  if (sig_kind == DataTypeKind::kImplicit || sig_kind == DataTypeKind::kNamed)
    return;
  DataType port_dt{};
  port_dt.kind = port_kind;
  DataType sig_dt{};
  sig_dt.kind = sig_kind;
  if (!IsAssignmentCompatible(sig_dt, port_dt)) {
    ctx.diag.Error(ctx.item->loc,
                   std::format("port connection type is not assignment "
                               "compatible with port '{}'",
                               binding_port_name),
                   Subclause("23.3.3"));
  }
}

static void CheckExplicitRefPortEquivalence(
    const PortBindCtx& ctx, const Expr* conn_expr, const RtlirPort& port,
    std::string_view binding_port_name) {
  if (port.direction != Direction::kRef ||
      ctx.var_types.count(conn_expr->text) == 0 ||
      ctx.net_names.count(conn_expr->text) != 0)
    return;
  uint32_t sig_width = FindSignalWidth(conn_expr->text, ctx.parent_mod);
  if (sig_width != 0 && sig_width != port.width) {
    ctx.diag.Error(ctx.item->loc,
                   std::format("ref port '{}' requires an equivalent variable "
                               "data type (port width {}, connection width {})",
                               binding_port_name, port.width, sig_width),
                   Subclause("23.3.3.2"));
  }
}

void CheckExplicitIdentifierConnection(const PortBindCtx& ctx,
                                       const Expr* conn_expr,
                                       const RtlirPort& port,
                                       std::string_view binding_port_name) {
  CheckExplicitConnAssignCompatible(ctx, conn_expr, port, binding_port_name);
  CheckExplicitRefPortEquivalence(ctx, conn_expr, port, binding_port_name);
  CheckDirectionalConnectionLegality(
      ctx, IdentConnection{port.direction, conn_expr->text, binding_port_name,
                           port.is_var});
}

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

bool DissimilarNetResultIsInternal(NetType internal, NetType external) {
  static constexpr bool kInternalWinsTable[9][9] = {
      {false, false, false, false, false, false, false, false, false},
      {true, false, false, false, false, false, false, false, false},
      {true, false, false, false, false, false, false, false, false},
      {true, false, false, false, false, false, false, false, false},
      {true, false, false, true, false, false, false, false, false},
      {true, false, false, true, false, false, false, false, false},
      {true, true, true, true, true, true, false, false, false},
      {true, true, true, true, true, true, true, false, false},
      {true, true, true, true, true, true, true, false, false},
  };
  int ig = NetTypeGroup(internal);
  int eg = NetTypeGroup(external);
  if (ig < 0 || eg < 0) return false;
  return kInternalWinsTable[ig][eg];
}

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
                             port.name, inst.module_name),
                 Subclause("23.3.3.2"));
    }
  }
}

std::string_view ConnectedInterfaceName(const Expr* conn) {
  if (conn == nullptr) return {};
  if (conn->kind == ExprKind::kIdentifier) return conn->text;
  if (conn->kind == ExprKind::kMemberAccess && conn->lhs != nullptr &&
      conn->lhs->kind == ExprKind::kIdentifier && conn->rhs != nullptr &&
      conn->rhs->kind == ExprKind::kIdentifier) {
    return conn->lhs->text;
  }
  if (conn->kind == ExprKind::kSelect && conn->base != nullptr &&
      conn->base->kind == ExprKind::kIdentifier && conn->index != nullptr &&
      conn->index_end == nullptr) {
    return conn->base->text;
  }
  return {};
}

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

void CheckInterfacePortsConnected(const PortBindCtx& ctx,
                                  const std::vector<RtlirPort>& child_ports,
                                  const RtlirModuleInst& inst) {
  for (const auto& port : child_ports) {
    if (!port.is_interface_port) continue;
    CheckOneInterfacePortConnected(ctx, port, inst);
  }
}

void Elaborator::CheckPortModportConsistency(const PortBindScope& scope,
                                             const RtlirPortBinding& binding,
                                             const Expr* conn_expr,
                                             const RtlirPort* child_port) {
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
                    binding.port_name, header_modport, connection_modport),
        Subclause("25.5"));
  }
}

void Elaborator::PrepareExplicitConnNet(const PortBindScope& scope,
                                        const ExplicitPortBind& bind) {
  const Expr* conn_expr = bind.conn_expr;
  if (!conn_expr || conn_expr->kind != ExprKind::kIdentifier) return;
  bool names_interface =
      !FindBlockInterface(conn_expr->text, gen_prefix_scopes_,
                          interface_inst_types_)
           .empty();
  if (bind.is_implicit) {
    if (!IsNameDeclared(conn_expr->text, scope.parent_mod) &&
        !ImportBringsInSignal(scope.parent_mod, unit_, conn_expr->text, true) &&
        !names_interface) {
      diag_.Error(
          scope.item->loc,
          std::format("implicit named port connection '.{}' requires "
                      "signal '{}' to be declared in the instantiating scope",
                      bind.port_name, conn_expr->text),
          Subclause("23.3.2.3"));
    }
  } else if (!names_interface) {
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
                      item->inst_ports.size()),
          Subclause("23.3.2.1"));
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
    diag_.Error(item->loc,
                std::format("port '{}' not found on module '{}'",
                            bind.port_name, inst.module_name),
                Subclause("23.3.2.2"));
    return false;
  }
  if (bind.is_implicit && port->is_interface_port &&
      port->interface_type_name.empty()) {
    diag_.Error(item->loc,
                std::format("implicit .{} port connection cannot reference "
                            "generic interface port '{}' of module '{}'",
                            bind.port_name, port->name, inst.module_name),
                Subclause("25.3.3"));
  }

  binding.direction = port->direction;
  binding.width = port->width;
  binding.port_expr = port->port_expr;
  if (bind.is_implicit && bind.conn_expr &&
      IsNameDeclared(bind.conn_expr->text, scope.parent_mod)) {
    CheckImplicitNamedPortNetTypes(kPortCtx, bind.port_name, bind.conn_expr,
                                   port);
  }
  CheckExplicitNamedPortNetTypes(kPortCtx, bind.is_implicit, bind.conn_expr,
                                 port, binding.port_name);
  return true;
}

static bool IsPositionalLvaluePattern(const Expr* pattern) {
  if (!pattern->pattern_keys.empty()) return false;
  return std::ranges::all_of(pattern->elements, [](const Expr* item) {
    return item->kind == ExprKind::kIdentifier ||
           item->kind == ExprKind::kSelect ||
           item->kind == ExprKind::kMemberAccess ||
           item->kind == ExprKind::kConcatenation;
  });
}

static bool IllegalPatternPortConnection(const Expr* conn_expr,
                                         Direction direction,
                                         const RtlirPort* port) {
  if (conn_expr->kind != ExprKind::kAssignmentPattern) return false;
  bool aggregate =
      port != nullptr && (port->data_kind == DataTypeKind::kStruct ||
                          port->data_kind == DataTypeKind::kUnion ||
                          port->num_unpacked_dims > 0 || port->type_is_array);
  if (direction == Direction::kInput) return !aggregate;
  return direction != Direction::kOutput || !aggregate ||
         !IsPositionalLvaluePattern(conn_expr);
}

static void CheckExplicitIdentifierOrInterfacePort(const PortBindCtx& ctx,
                                                   const Expr* conn_expr,
                                                   const RtlirPort* port,
                                                   std::string_view port_name) {
  if (!conn_expr || !port || port->is_interface_port) return;
  if (conn_expr->kind == ExprKind::kIdentifier) {
    CheckExplicitIdentifierConnection(ctx, conn_expr, *port, port_name);
  } else {
    CheckInoutConnectionParts(ctx, conn_expr, *port, port_name);
  }
}

void Elaborator::CheckExplicitConnLegality(const PortBindScope& scope,
                                           const ExplicitPortBind& bind) {
  const Expr* conn_expr = bind.conn_expr;
  const RtlirPortBinding& binding = bind.binding;
  const RtlirPort* port = bind.child_port;

  const PortBindCtx kPortCtx{diag_,
                             scope.item,
                             scope.parent_mod,
                             nettype_net_names_,
                             var_types_,
                             net_names_,
                             interconnect_names_,
                             interface_inst_types_,
                             scope.inst.resolved->is_checker};

  CheckExplicitIdentifierOrInterfacePort(kPortCtx, conn_expr, port,
                                         binding.port_name);

  if (conn_expr && binding.direction != Direction::kInput &&
      ConnectionHasReplication(conn_expr)) {
    diag_.Error(conn_expr->range.start,
                "replication shall not appear in an output or inout "
                "port connection",
                Subclause("11.4.12.1"));
  }

  if (conn_expr &&
      IllegalPatternPortConnection(conn_expr, binding.direction, port)) {
    diag_.Error(conn_expr->range.start,
                "an assignment pattern cannot be connected to this port",
                Subclause("10.8"));
  } else if (conn_expr && port &&
             port->unpacked_dim_sizes.size() == port->num_unpacked_dims) {
    ArrayPatternCheck{typedefs_, aggregate_typedef_names_, var_types_, diag_}
        .CheckSized(conn_expr, *port->declared_type, port->unpacked_dim_sizes,
                    conn_expr->range.start);
  }

  if (conn_expr && binding.direction != Direction::kInput &&
      binding.direction != Direction::kRef &&
      (!port || !port->is_interface_port)) {
    RecordOutputPortDrivenVariables(conn_expr, scope.item->loc);
  }
}

void Elaborator::RecordOutputPortDrivenVariables(const Expr* conn_expr,
                                                 SourceLoc loc) {
  std::vector<const Expr*> worklist{conn_expr};
  while (!worklist.empty()) {
    const Expr* e = worklist.back();
    worklist.pop_back();
    if (e == nullptr) continue;
    if (e->kind == ExprKind::kConcatenation ||
        e->kind == ExprKind::kAssignmentPattern) {
      for (const Expr* el : e->elements) worklist.push_back(el);
      continue;
    }
    if (e->kind != ExprKind::kIdentifier) continue;
    if (net_names_.count(e->text) != 0) continue;
    if (!output_port_targets_.emplace(e->text, loc).second) {
      diag_.Error(
          loc, std::format("variable '{}' driven by multiple outputs", e->text),
          Subclause("23.3.3.2"));
    }
  }
}

void Elaborator::SynthesizeExplicitDefault(const PortBindScope& scope,
                                           ExplicitPortBind& bind) {
  RtlirPortBinding& binding = bind.binding;
  const RtlirPort* port = bind.child_port;
  if (binding.direction != Direction::kInput) return;
  binding.unconnected = binding.connection == nullptr;

  if (scope.is_ordered && !binding.connection && port && port->default_value) {
    binding.connection = port->default_value;
  }
  if (scope.has_pull && !binding.connection) {
    binding.connection = MakePullExpr(scope.inst.resolved->unconnected_drive);
  }
  if (!binding.connection && port && IsNetPort(*port)) {
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

  ReportNonEquivalentImplicitConnection(diag_, item->loc, true, port,
                                        parent_mod);
  NetType pnet = PortNetType(port.type_kind);
  if (pnet != NetType::kNone) {
    NetType snet = FindSignalNetType(port.name, parent_mod);
    bool declared_interconnect =
        interconnect_names_.count(port.name) != 0 || port.is_interconnect;
    if (snet != NetType::kNone && snet != pnet &&
        snet != NetType::kInterconnect && !declared_interconnect) {
      diag_.Error(item->loc,
                  std::format("implicit .* port connection '.{}' between "
                              "dissimilar net types",
                              port.name),
                  Subclause("23.3.2.4"));
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
      binding.direction != Direction::kRef &&
      net_names_.count(port.name) == 0 &&
      !output_port_targets_.emplace(port.name, item->loc).second) {
    diag_.Error(
        item->loc,
        std::format("variable '{}' driven by multiple outputs", port.name),
        Subclause("23.3.3.2"));
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
  binding.port_expr = port.port_expr;

  if (port.is_interface_port) {
    if (port.interface_type_name.empty()) {
      diag_.Error(item->loc,
                  std::format("implicit .* port connection cannot reference "
                              "generic interface port '{}' of module '{}'",
                              port.name, inst.module_name),
                  Subclause("25.3.3"));
    } else if (interface_inst_types_.count(port.name)) {
      auto* expr = arena_.Create<Expr>();
      expr->kind = ExprKind::kIdentifier;
      expr->text = port.name;
      binding.connection = expr;
    }
  } else if (IsNameDeclared(port.name, parent_mod) ||
             ImportBringsInSignal(parent_mod, unit_, port.name, false)) {
    BindWildcardDeclaredPort(scope, port, binding);
  } else if (port.default_value) {
    binding.connection = port.default_value;
    binding.unconnected = true;
  } else if (port.direction == Direction::kInput) {
    binding.connection = DefaultInputConnection(
        arena_, port, scope.has_pull, scope.inst.resolved->unconnected_drive);
    binding.unconnected = true;
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
    binding.port_expr = port.port_expr;
    binding.unconnected = true;

    if (port.default_value) {
      binding.connection = port.default_value;
    } else {
      binding.connection = DefaultInputConnection(
          arena_, port, scope.has_pull, scope.inst.resolved->unconnected_drive);
    }

    if (binding.connection) {
      inst.port_bindings.push_back(binding);
    }
  }
}

}  // namespace delta
