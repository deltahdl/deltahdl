#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_port_binding_internal.h"
#include "elaborator/interconnect_merges.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/sdf_annotate_calls.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

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
                                binding.port_name, inst.module_name),
                    Subclause("23.3.3.1"));
    }

    if (binding.direction == Direction::kOutput && binding.connection &&
        binding.connection->kind == ExprKind::kIdentifier &&
        cont_assign_targets_.count(DeclaredScopedName(
            binding.connection->text, gen_prefix_scopes_, declared_names_))) {
      diag_.Warning(
          loc,
          std::format("port '{}' is declared as output but its connection "
                      "'{}' is also driven externally",
                      binding.port_name, binding.connection->text),
          Subclause("23.3.3.1"));
    }
  }
}

void CoerceDrivenInputPorts(RtlirModuleInst& inst, const RtlirModule* parent) {
  if (inst.resolved == nullptr || parent == nullptr) return;
  std::unordered_set<std::string_view> driven;
  for (const auto& ca : inst.resolved->assigns) {
    if (ca.lhs && ca.lhs->kind == ExprKind::kIdentifier) {
      driven.insert(ca.lhs->text);
    }
  }
  std::unordered_set<std::string_view> parent_nets;
  for (const auto& net : parent->nets) parent_nets.insert(net.name);
  for (auto& binding : inst.port_bindings) {
    if (binding.direction != Direction::kInput ||
        !driven.contains(binding.port_name) || binding.connection == nullptr ||
        binding.connection->kind != ExprKind::kIdentifier ||
        !parent_nets.contains(binding.connection->text)) {
      continue;
    }
    const auto& ports = inst.resolved->ports;
    auto port = std::find_if(ports.begin(), ports.end(), [&](const auto& p) {
      return p.name == binding.port_name;
    });
    if (port == ports.end() || port->is_var) continue;
    binding.direction = Direction::kInout;
  }
}

static const RtlirPort* FindChildPortByName(
    const std::vector<RtlirPort>& child_ports, std::string_view name) {
  auto port_it =
      std::find_if(child_ports.begin(), child_ports.end(),
                   [&](const RtlirPort& p) { return p.name == name; });
  if (port_it == child_ports.end()) return nullptr;
  return &*port_it;
}

static const RtlirPort* FindBoundChildPort(
    const std::vector<RtlirPort>& child_ports,
    const RtlirPortBinding& binding) {
  if (!binding.connection) return nullptr;
  return FindChildPortByName(child_ports, binding.port_name);
}

static bool PortLeftUnconnected(const std::vector<RtlirPort>& child_ports,
                                const ModuleItem* item,
                                std::string_view port_name) {
  bool is_ordered =
      !item->inst_ports.empty() && item->inst_ports[0].first.empty();
  if (is_ordered) {
    size_t idx = 0;
    for (; idx < child_ports.size(); ++idx) {
      if (child_ports[idx].name == port_name) break;
    }
    return idx >= item->inst_ports.size();
  }
  for (const auto& [pname, conn] : item->inst_ports) {
    (void)conn;
    if (pname == port_name) return false;
  }
  return true;
}

void Elaborator::CheckUwirePortMerge(RtlirModuleInst& inst,
                                     const ModuleItem* item,
                                     RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (auto& binding : inst.port_bindings) {
    const RtlirPort* port_it = FindBoundChildPort(child_ports, binding);
    if (!port_it) continue;
    if (PortLeftUnconnected(child_ports, item, binding.port_name)) continue;

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

    binding.uwire_net_join =
        (internal_net != NetType::kNone) && external_is_net;
    if (!binding.uwire_net_join) {
      WarnUwireNotMerged(diag_, item->loc, binding.port_name, inst.inst_name);
    }
  }
}

void Elaborator::CheckInterconnectPortMerge(const RtlirModuleInst& inst,
                                            const ModuleItem* item,
                                            RtlirModule* mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    const RtlirPort* port_it = FindBoundChildPort(child_ports, binding);
    if (!port_it) continue;

    const Expr* conn = binding.connection;
    const InterconnectMerges::Net kOuter{mod, conn->text};
    const InterconnectMerges::Net kInner{inst.resolved, binding.port_name};
    const bool kOuterIsInterconnect =
        conn->kind == ExprKind::kIdentifier &&
        interconnect_names_.count(conn->text) != 0;
    if (port_it->is_interconnect && kOuterIsInterconnect) {
      interconnect_merges_.Join(kOuter, kInner, item->loc, binding.port_name,
                                inst.inst_name);
    } else if (port_it->is_interconnect) {
      interconnect_merges_.MarkTyped(kInner,
                                     FindSignalNetType(conn->text, mod));
    } else if (kOuterIsInterconnect) {
      interconnect_merges_.MarkTyped(kOuter, port_it->net_type);
    }
  }
}

void Elaborator::ResolveInterconnectPrimitiveTerminals(
    const std::vector<Expr*>& terminals, RtlirModule* mod) {
  for (const auto* term : terminals) {
    if (!term || term->kind != ExprKind::kIdentifier) continue;
    if (interconnect_names_.count(term->text) == 0) continue;
    interconnect_merges_.MarkTyped({mod, term->text}, NetType::kNone);
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

struct ConnectedShape {
  uint32_t num_dims = 0;
  std::vector<uint32_t> sizes;
};

static void CheckUnpackedArrayPortBinding(
    DiagEngine& diag, const ModuleItem* item, const RtlirPortBinding& binding,
    const RtlirPort* port_it, const std::optional<ConnectedShape>& conn) {
  if (!conn) {
    diag.Error(item->loc,
               std::format("unpacked array port '{}' requires a matching "
                           "unpacked array connection",
                           binding.port_name),
               Subclause("23.3.3.5"));
    return;
  }

  if (conn->num_dims != port_it->num_unpacked_dims) {
    diag.Error(
        item->loc,
        std::format("unpacked array port '{}' has {} unpacked dimension(s) "
                    "but connection has {}",
                    binding.port_name, port_it->num_unpacked_dims,
                    conn->num_dims),
        Subclause("23.3.3.5"));
    return;
  }

  for (uint32_t d = 0; d < port_it->num_unpacked_dims; ++d) {
    if (d < port_it->unpacked_dim_sizes.size() && d < conn->sizes.size() &&
        conn->sizes[d] != 0 &&
        port_it->unpacked_dim_sizes[d] != conn->sizes[d]) {
      diag.Error(
          item->loc,
          std::format("unpacked array port '{}' dimension {} has size {} "
                      "but connection has size {}",
                      binding.port_name, d, port_it->unpacked_dim_sizes[d],
                      conn->sizes[d]),
          Subclause("23.3.3.5"));
      break;
    }
  }
}

using ArrayInfoMap =
    std::unordered_map<std::string_view, Elaborator::VarArrayInfo>;
static const Elaborator::VarArrayInfo* ConnectedArrayInfo(
    const Expr* connection, const ArrayInfoMap& vars,
    const ArrayInfoMap& nets) {
  if (connection == nullptr || connection->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  if (auto it = vars.find(connection->text); it != vars.end()) {
    return &it->second;
  }
  auto it = nets.find(connection->text);
  return it != nets.end() ? &it->second : nullptr;
}

static uint32_t SliceWidth(const Expr* sel, const ScopeMap& scope) {
  if (sel->is_part_select_plus || sel->is_part_select_minus) {
    auto width = ConstEvalInt(sel->index_end, scope);
    return width && *width > 0 ? static_cast<uint32_t>(*width) : 0;
  }
  auto left = ConstEvalInt(sel->index, scope);
  auto right = ConstEvalInt(sel->index_end, scope);
  if (!left || !right) return 0;
  return static_cast<uint32_t>(std::abs(*left - *right) + 1);
}

static std::optional<ConnectedShape> ConnectedArrayShape(
    const Expr* connection, const ArrayInfoMap& vars, const ArrayInfoMap& nets,
    const ScopeMap& scope) {
  std::vector<const Expr*> selects;
  const Expr* base = connection;
  while (base != nullptr && base->kind == ExprKind::kSelect) {
    selects.push_back(base);
    base = base->base;
  }
  const Elaborator::VarArrayInfo* info = ConnectedArrayInfo(base, vars, nets);
  if (info == nullptr) return std::nullopt;
  ConnectedShape shape{info->num_unpacked_dims, info->dim_sizes};
  shape.sizes.resize(shape.num_dims, 0);
  uint32_t dim = 0;
  for (auto it = selects.rbegin(); it != selects.rend(); ++it) {
    if (dim >= shape.num_dims) return std::nullopt;
    if ((*it)->index_end == nullptr) {
      shape.sizes.erase(shape.sizes.begin() + dim);
      --shape.num_dims;
      continue;
    }
    shape.sizes[dim++] = SliceWidth(*it, scope);
  }
  return shape;
}

static uint32_t InstanceArrayDimSize(const Expr* left, const Expr* right,
                                     const ScopeMap& scope) {
  auto l = ConstEvalInt(left, scope);
  if (!l) return 0;
  int64_t size = *l;
  if (right != nullptr) {
    auto r = ConstEvalInt(right, scope);
    if (!r) return 0;
    size = std::abs(*l - *r) + 1;
  }
  return size > 0 ? static_cast<uint32_t>(size) : 0;
}

static const ModuleItem* InstanceArrayItem(std::string_view name,
                                           const ModuleDecl* parent) {
  if (parent == nullptr) return nullptr;
  for (const ModuleItem* inst : parent->items) {
    if (inst->kind == ModuleItemKind::kModuleInst && inst->inst_name == name &&
        !inst->inst_dims.empty()) {
      return inst;
    }
  }
  return nullptr;
}

static std::optional<ConnectedShape> InterfaceInstanceArrayShape(
    const Expr* connection, const ModuleDecl* parent, const ScopeMap& scope) {
  if (connection == nullptr || connection->kind != ExprKind::kIdentifier) {
    return std::nullopt;
  }
  const ModuleItem* inst = InstanceArrayItem(connection->text, parent);
  if (inst == nullptr) return std::nullopt;
  ConnectedShape shape;
  for (const auto& [left, right] : inst->inst_dims) {
    shape.sizes.push_back(InstanceArrayDimSize(left, right, scope));
  }
  shape.num_dims = static_cast<uint32_t>(shape.sizes.size());
  return shape;
}

struct SignalSigning {
  bool is_signed;
  bool is_4state;
};

static std::optional<SignalSigning> FindSignalSigning(std::string_view name,
                                                      const RtlirModule* mod) {
  for (const auto& var : mod->variables) {
    if (var.name == name) return SignalSigning{var.is_signed, var.is_4state};
  }
  for (const auto& net : mod->nets) {
    if (net.name == name) return SignalSigning{net.is_signed, true};
  }
  return std::nullopt;
}

static bool SigningOrStatesDiffer(const RtlirPort& port, std::string_view name,
                                  const RtlirModule* parent) {
  auto signal = FindSignalSigning(name, parent);
  if (!signal) return false;
  DataTypeKind kind = port.data_kind != DataTypeKind::kImplicit
                          ? port.data_kind
                          : port.type_kind;
  bool port_4state = !port.is_var || Is4stateType(kind);
  return signal->is_signed != port.is_signed ||
         signal->is_4state != port_4state;
}

bool PortAndSignalDiffer(const RtlirPort& port, std::string_view name,
                         const RtlirModule* parent) {
  uint32_t sig_width = FindSignalWidth(name, parent);
  return (sig_width != 0 && sig_width != port.width) ||
         SigningOrStatesDiffer(port, name, parent);
}

void ReportNonEquivalentImplicitConnection(DiagEngine& diag, SourceLoc loc,
                                           bool is_wildcard,
                                           const RtlirPort& port,
                                           const RtlirModule* parent) {
  std::string_view form = is_wildcard ? ".*" : "named";
  std::string_view rule = is_wildcard ? "23.3.2.4" : "23.3.2.3";
  uint32_t sig_width = FindSignalWidth(port.name, parent);
  if (sig_width != 0 && sig_width != port.width) {
    diag.Error(loc,
               std::format("implicit {} port connection '.{}' requires "
                           "equivalent data types (port width {}, signal "
                           "width {})",
                           form, port.name, port.width, sig_width),
               Subclause(rule));
    return;
  }
  if (!SigningOrStatesDiffer(port, port.name, parent)) return;
  diag.Error(loc,
             std::format("implicit {} port connection '.{}' requires "
                         "equivalent data types (the port and the signal "
                         "differ in signing or in their number of states)",
                         form, port.name),
             Subclause(rule));
}

static bool PackageDeclaresSignal(const CompilationUnit* unit,
                                  std::string_view pkg_name,
                                  std::string_view name) {
  auto declares = [name](const ModuleItem* item) {
    return (item->kind == ModuleItemKind::kVarDecl ||
            item->kind == ModuleItemKind::kNetDecl) &&
           item->name == name;
  };
  return std::ranges::any_of(unit->packages, [&](const PackageDecl* pkg) {
    return pkg->name == pkg_name && std::ranges::any_of(pkg->items, declares);
  });
}

bool ImportBringsInSignal(const RtlirModule* mod, const CompilationUnit* unit,
                          std::string_view name, bool wildcard_counts) {
  return std::ranges::any_of(mod->imports, [&](const RtlirImport& imp) {
    bool names_it = imp.is_wildcard ? wildcard_counts : imp.item_name == name;
    return names_it && imp.scope_prefix.empty() &&
           PackageDeclaresSignal(unit, imp.package_name, name);
  });
}

void Elaborator::ValidateUnpackedArrayPorts(const RtlirModuleInst& inst,
                                            const ModuleItem* item,
                                            RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;
  ScopeMap scope = BuildParamScope(parent_mod);

  for (const auto& binding : inst.port_bindings) {
    const RtlirPort* port_it =
        FindChildPortByName(child_ports, binding.port_name);
    if (!port_it) continue;
    if (port_it->num_unpacked_dims == 0) continue;
    if (binding.connection != nullptr &&
        binding.connection->kind == ExprKind::kAssignmentPattern)
      continue;
    CheckUnpackedArrayPortBinding(
        diag_, item, binding, port_it,
        port_it->is_interface_port
            ? InterfaceInstanceArrayShape(binding.connection,
                                          FindModule(parent_mod->name), scope)
            : ConnectedArrayShape(binding.connection, var_array_info_,
                                  net_array_info_, scope));
  }
}

struct ConnArrayShape {
  uint32_t num_dims;
  const std::vector<uint32_t>* dim_sizes;
};

static void CheckInstanceArrayUnpackedConn(
    const PortBindCtx& ctx, const RtlirPortBinding& binding,
    const RtlirPort* port_it, const ConnArrayShape& conn,
    const std::vector<uint32_t>& inst_dim_sizes) {
  uint32_t expected_dims =
      static_cast<uint32_t>(inst_dim_sizes.size()) + port_it->num_unpacked_dims;
  if (conn.num_dims != expected_dims) {
    ctx.diag.Error(ctx.item->loc,
                   std::format("unpacked array connection to port '{}' has {} "
                               "dimension(s) but expected {}",
                               binding.port_name, conn.num_dims, expected_dims),
                   Subclause("23.3.3.5"));
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
                                 inst_dim_sizes[d]),
                     Subclause("23.3.3.5"));
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
                                 port_it->unpacked_dim_sizes[d]),
                     Subclause("23.3.3.5"));
      return;
    }
  }
}

namespace {

struct InstArrayConnEnv {
  const RtlirModule* parent_mod;
  const std::vector<uint32_t>& inst_dim_sizes;
  uint32_t total_instances;
  const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
      var_array_info;
};

void CheckOneInstanceArrayBinding(const PortBindCtx& ctx,
                                  const RtlirPortBinding& binding,
                                  const RtlirPort* port_it,
                                  const InstArrayConnEnv& env) {
  bool conn_is_unpacked = false;
  uint32_t conn_num_dims = 0;
  const std::vector<uint32_t>* conn_dim_sizes_ptr = nullptr;
  uint32_t conn_width = 0;

  if (binding.connection->kind == ExprKind::kIdentifier) {
    auto it = env.var_array_info.find(binding.connection->text);
    if (it != env.var_array_info.end()) {
      conn_is_unpacked = true;
      conn_num_dims = it->second.num_unpacked_dims;
      conn_dim_sizes_ptr = &it->second.dim_sizes;
    }
    conn_width = FindSignalWidth(binding.connection->text, env.parent_mod);
  }

  if (conn_is_unpacked) {
    CheckInstanceArrayUnpackedConn(
        ctx, binding, port_it,
        ConnArrayShape{conn_num_dims, conn_dim_sizes_ptr}, env.inst_dim_sizes);
    return;
  }
  if (conn_width != 0 && conn_width != port_it->width) {
    uint32_t expected_width = port_it->width * env.total_instances;
    if (conn_width != expected_width) {
      ctx.diag.Error(
          ctx.item->loc,
          std::format("packed array connection to port '{}' has width {} "
                      "but expected {} ({} instances * port width {})",
                      binding.port_name, conn_width, expected_width,
                      env.total_instances, port_it->width),
          Subclause("23.3.3.5"));
    }
  }
}

}  // namespace

void Elaborator::ValidateInstanceArrayPorts(
    const RtlirModuleInst& inst, const ModuleItem* item,
    RtlirModule* parent_mod, const std::vector<uint32_t>& inst_dim_sizes,
    uint32_t total_instances) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;
  const PortBindCtx kPortCtx{
      diag_,      item,       parent_mod,          nettype_net_names_,
      var_types_, net_names_, interconnect_names_, interface_inst_types_};
  const InstArrayConnEnv kEnv{parent_mod, inst_dim_sizes, total_instances,
                              var_array_info_};

  for (const auto& binding : inst.port_bindings) {
    const RtlirPort* port_it = FindBoundChildPort(child_ports, binding);
    if (!port_it) continue;
    CheckOneInstanceArrayBinding(kPortCtx, binding, port_it, kEnv);
  }
}

void ReportVariableOnInout(const PortBindCtx& ctx, std::string_view name,
                           std::string_view port_name, bool port_is_var) {
  if (ctx.var_types.count(name) == 0 || ctx.net_names.count(name) != 0) return;
  ctx.diag.Error(ctx.item->loc,
                 std::format("variable '{}' cannot be connected to inout port "
                             "'{}'",
                             name, port_name),
                 port_is_var ? Subclause("23.3.3.2") : Subclause("23.3.3.3"));
}

void CheckInoutConnectionParts(const PortBindCtx& ctx, const Expr* conn_expr,
                               const RtlirPort& port,
                               std::string_view port_name) {
  if (port.direction != Direction::kInout) return;
  if (conn_expr->kind == ExprKind::kConcatenation) {
    for (const Expr* part : conn_expr->elements)
      CheckInoutConnectionParts(ctx, part, port, port_name);
    return;
  }
  const Expr* object = conn_expr;
  while (object->kind == ExprKind::kSelect) object = object->base;
  ReportVariableOnInout(ctx, object->text, port_name, port.is_var);
}

}  // namespace delta
