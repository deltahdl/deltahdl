#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_port_binding_internal.h"
#include "elaborator/rtlir.h"
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
        cont_assign_targets_.count(binding.connection->text)) {
      diag_.Warning(
          loc,
          std::format("port '{}' is declared as output but its connection "
                      "'{}' is also driven externally",
                      binding.port_name, binding.connection->text),
          Subclause("23.3.3.1"));
    }
  }
}

// §23.3.3.1 (printed page 747): "A port that is declared as input (output)
// but used as an output (input) or inout may be coerced to inout. If not
// coerced to inout, a warning shall be issued." An input port the module
// drives, `module m(input wire a); assign a = 1'b1;`, is coerced where both
// sides are nets -- §23.3.3.3 lets an inout connect to a net and never to a
// variable -- so the connection becomes the one net an inout's is and the
// module's driver reaches the parent's w. CheckPortCoercion has warned by
// then; the warning is kept, being what reports the port's use.
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

// Looks up a child port by name; returns nullptr when no port matches.
static const RtlirPort* FindChildPortByName(
    const std::vector<RtlirPort>& child_ports, std::string_view name) {
  auto port_it =
      std::find_if(child_ports.begin(), child_ports.end(),
                   [&](const RtlirPort& p) { return p.name == name; });
  if (port_it == child_ports.end()) return nullptr;
  return &*port_it;
}

// Resolves the child port a binding connects to; nullptr when the binding has
// no connection or names no matching child port.
static const RtlirPort* FindBoundChildPort(
    const std::vector<RtlirPort>& child_ports,
    const RtlirPortBinding& binding) {
  if (!binding.connection) return nullptr;
  return FindChildPortByName(child_ports, binding.port_name);
}

// True when this child port carries no user-supplied connection in the
// instantiation, i.e. its binding was synthesized for an unconnected input
// port. §23.3.3.6: an unconnected uwire port has no second source to merge, so
// the single-source warning shall not fire for it. Explicit connections (named
// or positional, including non-identifier expressions) remain user-supplied.
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

void Elaborator::CheckUwirePortMerge(const RtlirModuleInst& inst,
                                     const ModuleItem* item,
                                     RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
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

    bool merged = (internal_net != NetType::kNone) && external_is_net;
    if (!merged) {
      diag_.Warning(
          item->loc,
          std::format("uwire net on port '{}' of instance '{}' is not "
                      "merged into a single net",
                      binding.port_name, inst.inst_name),
          Subclause("23.3.3.6"));
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
                      binding.port_name, inst.inst_name),
          Subclause("23.3.3.7.1"));
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

// Validates one unpacked-array port binding: the connection must be an
// identifier naming an unpacked array with matching dimension count and sizes.
// `conn_info` is the array the identifier names, null where it names none.
static void CheckUnpackedArrayPortBinding(
    DiagEngine& diag, const ModuleItem* item, const RtlirPortBinding& binding,
    const RtlirPort* port_it, const Elaborator::VarArrayInfo* conn) {
  if (conn == nullptr) {
    diag.Error(item->loc,
               std::format("unpacked array port '{}' requires a matching "
                           "unpacked array connection",
                           binding.port_name),
               Subclause("23.3.3.5"));
    return;
  }

  const auto& conn_info = *conn;
  if (conn_info.num_unpacked_dims != port_it->num_unpacked_dims) {
    diag.Error(
        item->loc,
        std::format("unpacked array port '{}' has {} unpacked dimension(s) "
                    "but connection has {}",
                    binding.port_name, port_it->num_unpacked_dims,
                    conn_info.num_unpacked_dims),
        Subclause("23.3.3.5"));
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
                      conn_info.dim_sizes[d]),
          Subclause("23.3.3.5"));
      break;
    }
  }
}

// §7.4.2 (printed page 154): "Net arrays are useful for connecting to ports
// of module instances", so the array an unpacked array port's connection names
// is a net array as readily as a variable one, and each is recorded apart.
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
    CheckUnpackedArrayPortBinding(
        diag_, item, binding, port_it,
        ConnectedArrayInfo(binding.connection, var_array_info_,
                           net_array_info_));
  }
}

// The connecting signal's unpacked-array shape: total dimension count and, when
// known, the per-dimension sizes consulted by the instance-array check.
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

// The instance-array connection environment for one binding: the instantiating
// module, the per-dimension instance-array sizes, the total instance count, and
// the parent-scope unpacked-array shapes consulted by the connection check.
struct InstArrayConnEnv {
  const RtlirModule* parent_mod;
  const std::vector<uint32_t>& inst_dim_sizes;
  uint32_t total_instances;
  const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
      var_array_info;
};

// §23.3.3.x classifies one instance-array port connection and dispatches to the
// unpacked-array shape check or the packed-array width check.
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

}  // namespace delta
