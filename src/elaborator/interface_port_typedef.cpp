#include "elaborator/interface_port_typedef.h"

#include <algorithm>
#include <cstddef>
#include <functional>
#include <string_view>

#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

std::string_view ConnectedActualName(const ModuleItem& inst, size_t index,
                                     std::string_view port) {
  const Expr* conn = nullptr;
  for (const auto& [name, actual] : inst.inst_ports) {
    if (name == port) conn = actual;
  }
  if (conn == nullptr && index < inst.inst_ports.size() &&
      inst.inst_ports[index].first.empty()) {
    conn = inst.inst_ports[index].second;
  }
  if (conn == nullptr) return inst.inst_wildcard ? port : std::string_view{};
  while (conn != nullptr && conn->kind != ExprKind::kIdentifier) {
    conn = conn->kind == ExprKind::kMemberAccess ? conn->lhs
           : conn->kind == ExprKind::kSelect     ? conn->base
                                                 : nullptr;
  }
  return conn != nullptr ? conn->text : std::string_view{};
}

}  // namespace

std::string_view InterfaceTypeOfPort(std::string_view port_name,
                                     const ModuleDecl& decl,
                                     const GenericPortInterfaces& generic) {
  auto port = std::ranges::find(decl.ports, port_name, &PortDecl::name);
  if (port != decl.ports.end() && !port->data_type.type_name.empty()) {
    return port->data_type.type_name;
  }
  auto it = generic.find(port_name);
  return it != generic.end() ? it->second : std::string_view{};
}

InterfacePortType InterfacePortTypedef(
    const ModuleItem& item, const ModuleDecl& decl,
    const GenericPortInterfaces& generic,
    const std::function<const ModuleDecl*(std::string_view)>& find_module) {
  InterfacePortType found;
  const std::string_view kType =
      InterfaceTypeOfPort(item.typedef_ifc_port, decl, generic);
  if (kType.empty()) return found;
  found.iface = find_module(kType);
  if (found.iface == nullptr) return found;
  auto it = std::ranges::find_if(found.iface->items, [&](const ModuleItem* i) {
    return i->kind == ModuleItemKind::kTypedef &&
           i->name == item.typedef_type.type_name;
  });
  if (it != found.iface->items.end()) found.typedef_item = *it;
  return found;
}

GenericPortInterfaces GenericPortInterfacesOf(
    const ModuleItem& inst, const ModuleDecl& child,
    const std::function<std::string_view(std::string_view)>&
        interface_of_actual) {
  GenericPortInterfaces found;
  for (size_t i = 0; i < child.ports.size(); ++i) {
    const PortDecl& port = child.ports[i];
    if (!port.is_interface_port || !port.data_type.type_name.empty()) continue;
    const std::string_view kType =
        interface_of_actual(ConnectedActualName(inst, i, port.name));
    if (!kType.empty()) found[port.name] = kType;
  }
  return found;
}

}  // namespace delta
