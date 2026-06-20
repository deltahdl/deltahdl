#include <algorithm>
#include <cstdint>
#include <format>
#include <functional>
#include <string_view>
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

}  // namespace

Expr* Elaborator::MakePullExpr(NetType drive) {
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kIntegerLiteral;
  expr->int_val = (drive == NetType::kTri1) ? 1 : 0;
  return expr;
}

Expr* Elaborator::MakeHighZExpr() {
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kUnbasedUnsizedLiteral;
  expr->text = "'z";
  return expr;
}

void Elaborator::BindPorts(RtlirModuleInst& inst, const ModuleItem* item,
                           RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;
  const bool has_pull = unit_->unconnected_drive != NetType::kWire;

  const bool is_ordered =
      !item->inst_ports.empty() && item->inst_ports[0].first.empty();

  // §23.3.3.2: connecting a child's port variable to an interconnect signal of
  // the instantiating module is illegal. The interconnect signal may be a local
  // interconnect net (recorded in interconnect_names_) or one of this module's
  // own interconnect ports threaded down through the hierarchy.
  auto connects_to_interconnect = [&](std::string_view conn_name) -> bool {
    if (interconnect_names_.count(conn_name)) return true;
    for (const auto& p : parent_mod->ports)
      if (p.name == conn_name && p.is_interconnect) return true;
    return false;
  };

  for (size_t i = 0; i < item->inst_ports.size(); ++i) {
    auto& [port_name, conn_expr] = item->inst_ports[i];
    const bool is_implicit =
        i < item->inst_ports_implicit.size() && item->inst_ports_implicit[i];

    if (conn_expr && conn_expr->kind == ExprKind::kIdentifier) {
      if (is_implicit) {
        if (!IsNameDeclared(conn_expr->text, parent_mod)) {
          diag_.Error(
              item->loc,
              std::format(
                  "implicit named port connection '.{}' requires "
                  "signal '{}' to be declared in the instantiating scope",
                  port_name, conn_expr->text));
        }
      } else if (!interface_inst_types_.count(conn_expr->text)) {
        MaybeCreateImplicitNet(conn_expr->text, item->loc, parent_mod);
      }
    }
    RtlirPortBinding binding;
    binding.connection = conn_expr;

    auto it = child_ports.end();
    if (is_ordered) {
      if (i < child_ports.size()) {
        it = child_ports.begin() + static_cast<ptrdiff_t>(i);
        binding.port_name = it->name;
      } else {
        diag_.Warning(
            item->loc,
            std::format("too many ordered port connections for module '{}'"
                        " (expected {}, got {})",
                        inst.module_name, child_ports.size(),
                        item->inst_ports.size()));
        break;
      }
    } else {
      binding.port_name = port_name;
      it =
          std::find_if(child_ports.begin(), child_ports.end(),
                       [&](const RtlirPort& p) { return p.name == port_name; });
    }

    if (it == child_ports.end()) {
      diag_.Warning(item->loc, std::format("port '{}' not found on module '{}'",
                                           port_name, inst.module_name));
      binding.direction = Direction::kInput;
      binding.width = 1;
    } else {
      binding.direction = it->direction;
      binding.width = it->width;

      if (is_implicit && conn_expr &&
          IsNameDeclared(conn_expr->text, parent_mod)) {
        uint32_t sig_width = FindSignalWidth(conn_expr->text, parent_mod);
        if (sig_width != 0 && sig_width != it->width) {
          diag_.Error(
              item->loc,
              std::format("implicit named port connection '.{}' requires "
                          "equivalent data types (port width {}, "
                          "signal width {})",
                          port_name, it->width, sig_width));
        }

        NetType pnet = PortNetType(it->type_kind);
        if (pnet != NetType::kNone) {
          NetType snet = FindSignalNetType(conn_expr->text, parent_mod);
          // 23.3.2.3: the implicit .name form escalates to an error precisely
          // in the cases where the equivalent explicit named connection would
          // merely warn (23.3.3.7). Net types that are equivalent (for example
          // the wire/tri aliases) are not dissimilar, so they neither warn nor
          // error here.
          if (snet != NetType::kNone && snet != NetType::kInterconnect &&
              !it->is_interconnect &&
              DissimilarNetTypeRequiresWarning(pnet, snet)) {
            diag_.Error(
                item->loc,
                std::format("implicit named port connection '.{}' between "
                            "dissimilar net types",
                            port_name));
          }
        }
      }

      if (!is_implicit && conn_expr &&
          conn_expr->kind == ExprKind::kIdentifier) {
        NetType pnet = PortNetType(it->type_kind);
        if (pnet != NetType::kNone) {
          NetType snet = FindSignalNetType(conn_expr->text, parent_mod);
          if (snet != NetType::kNone && snet != pnet) {
            if (DissimilarNetTypeRequiresWarning(pnet, snet)) {
              diag_.Warning(
                  item->loc,
                  std::format("port '{}' connected between dissimilar "
                              "net types",
                              binding.port_name));
            }
          }
        }
      }
    }

    if (conn_expr && conn_expr->kind == ExprKind::kIdentifier &&
        it != child_ports.end() && !it->is_interface_port) {
      DataTypeKind port_kind = NormalizeForCompatibility(it->type_kind);
      if (port_kind != DataTypeKind::kImplicit) {
        DataTypeKind sig_kind = DataTypeKind::kImplicit;
        auto vt = var_types_.find(conn_expr->text);
        if (vt != var_types_.end()) {
          sig_kind = NormalizeForCompatibility(vt->second);
        } else if (net_names_.count(conn_expr->text)) {
          sig_kind = DataTypeKind::kLogic;
        }
        if (sig_kind != DataTypeKind::kImplicit) {
          DataType port_dt{};
          port_dt.kind = port_kind;
          DataType sig_dt{};
          sig_dt.kind = sig_kind;
          if (!IsAssignmentCompatible(sig_dt, port_dt)) {
            diag_.Error(item->loc,
                        std::format("port connection type is not assignment "
                                    "compatible with port '{}'",
                                    binding.port_name));
          }
        }
      }

      if (it->direction == Direction::kInout &&
          nettype_net_names_.count(conn_expr->text)) {
        diag_.Error(
            item->loc,
            std::format("user-defined nettype signal '{}' cannot connect "
                        "to inout port '{}'",
                        conn_expr->text, binding.port_name));
      }

      if (it->direction == Direction::kInout &&
          var_types_.count(conn_expr->text) &&
          net_names_.count(conn_expr->text) == 0) {
        diag_.Error(item->loc,
                    std::format("variable '{}' cannot be connected to "
                                "inout port '{}'",
                                conn_expr->text, binding.port_name));
      }

      if (it->direction == Direction::kRef &&
          net_names_.count(conn_expr->text)) {
        diag_.Error(item->loc,
                    std::format("net '{}' cannot be connected to ref port "
                                "'{}'; ref port requires a variable",
                                conn_expr->text, binding.port_name));
      }

      if (it->is_var && connects_to_interconnect(conn_expr->text)) {
        diag_.Error(item->loc,
                    std::format("port variable '{}' cannot be connected to "
                                "interconnect '{}'",
                                binding.port_name, conn_expr->text));
      }
    }

    if (conn_expr && binding.direction != Direction::kInput) {
      std::function<bool(const Expr*)> has_rep = [&](const Expr* e) -> bool {
        if (!e) return false;
        if (e->kind == ExprKind::kReplicate) return true;
        if (e->kind == ExprKind::kConcatenation) {
          for (const auto* el : e->elements)
            if (has_rep(el)) return true;
        }
        return false;
      };
      if (has_rep(conn_expr)) {
        diag_.Error(conn_expr->range.start,
                    "replication shall not appear in an output or inout "
                    "port connection");
      }
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
      if (!output_port_targets_.emplace(name, item->loc).second) {
        diag_.Error(
            item->loc,
            std::format("variable '{}' driven by multiple outputs", name));
      }
    }

    if (is_ordered && !binding.connection &&
        binding.direction == Direction::kInput && it != child_ports.end() &&
        it->default_value) {
      binding.connection = it->default_value;
    }

    if (has_pull && !binding.connection &&
        binding.direction == Direction::kInput) {
      binding.connection = MakePullExpr(unit_->unconnected_drive);
    }

    if (!binding.connection && binding.direction == Direction::kInput &&
        it != child_ports.end() && !it->is_var &&
        PortNetType(it->type_kind) != NetType::kNone) {
      binding.connection = MakeHighZExpr();
    }

    // §25.5: a modport may be selected in the module header for an interface
    // port (e.g. `iface.target a`) and again in the instance connection
    // (`.a(inst.initiator)`). When both sites select one, they shall name the
    // same modport. Only the genuine both-specified case is checked: a bare
    // instance reference in the connection, or a header port without a modport,
    // leaves nothing to disagree about.
    if (it != child_ports.end() && it->is_interface_port && conn_expr &&
        conn_expr->kind == ExprKind::kMemberAccess && conn_expr->lhs &&
        conn_expr->lhs->kind == ExprKind::kIdentifier && conn_expr->rhs &&
        conn_expr->rhs->kind == ExprKind::kIdentifier) {
      std::string_view header_modport;
      if (const auto* child_decl = FindModule(inst.module_name)) {
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
            item->loc,
            std::format(
                "interface port '{}' selects modport '{}' in the module "
                "header but '{}' in the instance connection; both shall "
                "name the same modport",
                binding.port_name, header_modport, connection_modport));
      }
    }

    inst.port_bindings.push_back(binding);
  }

  if (item->inst_wildcard) {
    for (const auto& port : child_ports) {
      bool connected = false;
      for (const auto& [pname, _] : item->inst_ports) {
        if (pname == port.name) {
          connected = true;
          break;
        }
      }
      if (connected) continue;

      RtlirPortBinding binding;
      binding.port_name = port.name;
      binding.direction = port.direction;
      binding.width = port.width;

      if (port.is_interface_port) {
        if (port.interface_type_name.empty()) {
          diag_.Error(
              item->loc,
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

        if (port.direction == Direction::kInout &&
            nettype_net_names_.count(port.name)) {
          diag_.Error(
              item->loc,
              std::format("user-defined nettype signal '{}' cannot connect "
                          "to inout port '{}'",
                          port.name, port.name));
        }

        if (port.direction == Direction::kInout &&
            var_types_.count(port.name) && net_names_.count(port.name) == 0) {
          diag_.Error(item->loc,
                      std::format("variable '{}' cannot be connected to "
                                  "inout port '{}'",
                                  port.name, port.name));
        }

        if (port.direction == Direction::kRef && net_names_.count(port.name)) {
          diag_.Error(item->loc,
                      std::format("net '{}' cannot be connected to ref port "
                                  "'{}'; ref port requires a variable",
                                  port.name, port.name));
        }

        if (port.is_var && connects_to_interconnect(port.name)) {
          diag_.Error(item->loc,
                      std::format("port variable '{}' cannot be connected to "
                                  "interconnect '{}'",
                                  port.name, port.name));
        }

        auto* expr = arena_.Create<Expr>();
        expr->kind = ExprKind::kIdentifier;
        expr->text = port.name;
        binding.connection = expr;

        if (binding.direction != Direction::kInput &&
            net_names_.count(port.name) == 0) {
          if (!output_port_targets_.emplace(port.name, item->loc).second) {
            diag_.Error(item->loc,
                        std::format("variable '{}' driven by multiple outputs",
                                    port.name));
          }
        }
      } else if (port.default_value) {
        binding.connection = port.default_value;
      } else if (has_pull && port.direction == Direction::kInput) {
        binding.connection = MakePullExpr(unit_->unconnected_drive);
      } else if (port.direction == Direction::kInput && !port.is_var &&
                 PortNetType(port.type_kind) != NetType::kNone) {
        binding.connection = MakeHighZExpr();
      }

      if (binding.connection) {
        inst.port_bindings.push_back(binding);
      }
    }
  } else {
    size_t first_unconnected = is_ordered ? item->inst_ports.size() : 0;
    for (size_t i = first_unconnected; i < child_ports.size(); ++i) {
      const auto& port = child_ports[i];
      if (port.direction != Direction::kInput) continue;

      if (!is_ordered) {
        bool connected = false;
        for (const auto& [pname, _] : item->inst_ports) {
          if (pname == port.name) {
            connected = true;
            break;
          }
        }
        if (connected) continue;
      }

      RtlirPortBinding binding;
      binding.port_name = port.name;
      binding.direction = port.direction;
      binding.width = port.width;

      if (port.default_value) {
        binding.connection = port.default_value;
      } else if (has_pull) {
        binding.connection = MakePullExpr(unit_->unconnected_drive);
      } else if (!port.is_var &&
                 PortNetType(port.type_kind) != NetType::kNone) {
        binding.connection = MakeHighZExpr();
      }

      if (binding.connection) {
        inst.port_bindings.push_back(binding);
      }
    }
  }

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
      diag_.Error(item->loc,
                  std::format("ref port '{}' of module '{}' cannot be "
                              "left unconnected",
                              port.name, inst.module_name));
    }
  }

  for (const auto& port : child_ports) {
    if (!port.is_interface_port) continue;

    Expr* conn = nullptr;
    for (const auto& binding : inst.port_bindings) {
      if (binding.port_name == port.name) {
        conn = binding.connection;
        break;
      }
    }

    if (!conn) {
      diag_.Error(item->loc,
                  std::format("interface port '{}' of module '{}' cannot be "
                              "left unconnected",
                              port.name, inst.module_name));
      continue;
    }

    std::string_view conn_name;
    if (conn->kind == ExprKind::kIdentifier) {
      conn_name = conn->text;
    } else if (conn->kind == ExprKind::kMemberAccess && conn->lhs &&
               conn->lhs->kind == ExprKind::kIdentifier && conn->rhs &&
               conn->rhs->kind == ExprKind::kIdentifier) {
      conn_name = conn->lhs->text;
    } else {
      diag_.Error(item->loc,
                  std::format("interface port '{}' must be connected to an "
                              "interface instance or interface port",
                              port.name));
      continue;
    }

    std::string_view conn_ifc_type;

    auto iit = interface_inst_types_.find(conn_name);
    if (iit != interface_inst_types_.end()) {
      conn_ifc_type = iit->second;
    } else {
      bool is_ifc_port = false;
      for (const auto& pp : parent_mod->ports) {
        if (pp.name == conn_name && pp.is_interface_port) {
          conn_ifc_type = pp.interface_type_name;
          is_ifc_port = true;
          break;
        }
      }
      if (!is_ifc_port) {
        diag_.Error(item->loc,
                    std::format("interface port '{}' must be connected to an "
                                "interface instance or interface port",
                                port.name));
        continue;
      }
    }

    if (!port.interface_type_name.empty() && !conn_ifc_type.empty() &&
        port.interface_type_name != conn_ifc_type) {
      diag_.Error(
          item->loc,
          std::format("interface port '{}' requires interface type '{}' "
                      "but is connected to instance of type '{}'",
                      port.name, port.interface_type_name, conn_ifc_type));
    }
  }
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

void Elaborator::CheckUwirePortMerge(const RtlirModuleInst& inst,
                                     const ModuleItem* item,
                                     RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    if (!binding.connection) continue;

    auto port_it = std::find_if(
        child_ports.begin(), child_ports.end(),
        [&](const RtlirPort& p) { return p.name == binding.port_name; });
    if (port_it == child_ports.end()) continue;

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
                                            RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    if (!binding.connection) continue;

    auto port_it = std::find_if(
        child_ports.begin(), child_ports.end(),
        [&](const RtlirPort& p) { return p.name == binding.port_name; });
    if (port_it == child_ports.end()) continue;

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

void Elaborator::ValidateUnpackedArrayPorts(const RtlirModuleInst& inst,
                                            const ModuleItem* item,
                                            RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    auto port_it = std::find_if(
        child_ports.begin(), child_ports.end(),
        [&](const RtlirPort& p) { return p.name == binding.port_name; });
    if (port_it == child_ports.end()) continue;
    if (port_it->num_unpacked_dims == 0) continue;

    if (!binding.connection ||
        binding.connection->kind != ExprKind::kIdentifier) {
      diag_.Error(item->loc,
                  std::format("unpacked array port '{}' requires a matching "
                              "unpacked array connection",
                              binding.port_name));
      continue;
    }

    auto it = var_array_info_.find(binding.connection->text);
    if (it == var_array_info_.end()) {
      diag_.Error(item->loc,
                  std::format("unpacked array port '{}' requires a matching "
                              "unpacked array connection",
                              binding.port_name));
      continue;
    }

    const auto& conn_info = it->second;
    if (conn_info.num_unpacked_dims != port_it->num_unpacked_dims) {
      diag_.Error(
          item->loc,
          std::format("unpacked array port '{}' has {} unpacked dimension(s) "
                      "but connection has {}",
                      binding.port_name, port_it->num_unpacked_dims,
                      conn_info.num_unpacked_dims));
      continue;
    }

    for (uint32_t d = 0; d < port_it->num_unpacked_dims; ++d) {
      if (d < port_it->unpacked_dim_sizes.size() &&
          d < conn_info.dim_sizes.size() &&
          port_it->unpacked_dim_sizes[d] != conn_info.dim_sizes[d]) {
        diag_.Error(
            item->loc,
            std::format("unpacked array port '{}' dimension {} has size {} "
                        "but connection has size {}",
                        binding.port_name, d, port_it->unpacked_dim_sizes[d],
                        conn_info.dim_sizes[d]));
        break;
      }
    }
  }
}

void Elaborator::ValidateInstanceArrayPorts(
    const RtlirModuleInst& inst, const ModuleItem* item,
    RtlirModule* parent_mod, const std::vector<uint32_t>& inst_dim_sizes,
    uint32_t total_instances) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    if (!binding.connection) continue;

    auto port_it = std::find_if(
        child_ports.begin(), child_ports.end(),
        [&](const RtlirPort& p) { return p.name == binding.port_name; });
    if (port_it == child_ports.end()) continue;

    bool conn_is_unpacked = false;
    uint32_t conn_num_dims = 0;
    const std::vector<uint32_t>* conn_dim_sizes_ptr = nullptr;
    uint32_t conn_width = 0;

    if (binding.connection->kind == ExprKind::kIdentifier) {
      auto it = var_array_info_.find(binding.connection->text);
      if (it != var_array_info_.end()) {
        conn_is_unpacked = true;
        conn_num_dims = it->second.num_unpacked_dims;
        conn_dim_sizes_ptr = &it->second.dim_sizes;
      }
      conn_width = FindSignalWidth(binding.connection->text, parent_mod);
    }

    if (conn_is_unpacked) {
      uint32_t expected_dims = static_cast<uint32_t>(inst_dim_sizes.size()) +
                               port_it->num_unpacked_dims;
      if (conn_num_dims != expected_dims) {
        diag_.Error(
            item->loc,
            std::format("unpacked array connection to port '{}' has {} "
                        "dimension(s) but expected {}",
                        binding.port_name, conn_num_dims, expected_dims));
        continue;
      }
      if (conn_dim_sizes_ptr) {
        for (size_t d = 0; d < inst_dim_sizes.size(); ++d) {
          if (d < conn_dim_sizes_ptr->size() &&
              (*conn_dim_sizes_ptr)[d] != inst_dim_sizes[d]) {
            diag_.Error(
                item->loc,
                std::format("unpacked array connection to port '{}' "
                            "dimension {} has size {} but instance array "
                            "has size {}",
                            binding.port_name, d, (*conn_dim_sizes_ptr)[d],
                            inst_dim_sizes[d]));
            break;
          }
        }
        for (uint32_t d = 0; d < port_it->num_unpacked_dims; ++d) {
          uint32_t ci = static_cast<uint32_t>(inst_dim_sizes.size()) + d;
          if (ci < conn_dim_sizes_ptr->size() &&
              d < port_it->unpacked_dim_sizes.size() &&
              (*conn_dim_sizes_ptr)[ci] != port_it->unpacked_dim_sizes[d]) {
            diag_.Error(
                item->loc,
                std::format("unpacked array connection to port '{}' "
                            "port dimension {} has size {} but port "
                            "expects {}",
                            binding.port_name, d, (*conn_dim_sizes_ptr)[ci],
                            port_it->unpacked_dim_sizes[d]));
            break;
          }
        }
      }
    } else if (conn_width != 0 && conn_width != port_it->width) {
      uint32_t expected_width = port_it->width * total_instances;
      if (conn_width != expected_width) {
        diag_.Error(
            item->loc,
            std::format("packed array connection to port '{}' has width {} "
                        "but expected {} ({} instances * port width {})",
                        binding.port_name, conn_width, expected_width,
                        total_instances, port_it->width));
      }
    }
  }
}

}  // namespace delta
