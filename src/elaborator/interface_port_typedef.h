#pragma once

#include <functional>
#include <string_view>
#include <unordered_map>

#include "parser/ast_module.h"

namespace delta {

using GenericPortInterfaces =
    std::unordered_map<std::string_view, std::string_view>;

struct InterfacePortType {
  const PortDecl* port = nullptr;
  const ModuleDecl* iface = nullptr;
  const ModuleItem* typedef_item = nullptr;
};

std::string_view InterfaceTypeOfPort(std::string_view port_name,
                                     const ModuleDecl& decl,
                                     const GenericPortInterfaces& generic);

InterfacePortType InterfacePortTypedef(
    const ModuleItem& item, const ModuleDecl& decl,
    const GenericPortInterfaces& generic,
    const std::function<const ModuleDecl*(std::string_view)>& find_module);

GenericPortInterfaces GenericPortInterfacesOf(
    const ModuleItem& inst, const ModuleDecl& child,
    const std::function<std::string_view(std::string_view)>&
        interface_of_actual);

}  // namespace delta
