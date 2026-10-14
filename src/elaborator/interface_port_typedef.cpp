// §25.10: a type a module takes from an interface through its port.

#include "elaborator/interface_port_typedef.h"

#include <functional>
#include <string_view>

#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

const DataType* InterfacePortTypedefType(
    const ModuleItem* item, const ModuleDecl* decl,
    const std::function<const ModuleDecl*(std::string_view)>& find_module) {
  for (const PortDecl& port : decl->ports) {
    if (port.name != item->typedef_ifc_port) continue;
    const ModuleDecl* iface = find_module(port.data_type.type_name);
    if (iface == nullptr) return nullptr;
    for (const ModuleItem* it : iface->items) {
      if (it->kind == ModuleItemKind::kTypedef &&
          it->name == item->typedef_type.type_name) {
        return &it->typedef_type;
      }
    }
    return nullptr;
  }
  return nullptr;
}

}  // namespace delta
