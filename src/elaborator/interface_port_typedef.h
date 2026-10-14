#pragma once

#include <functional>
#include <string_view>

#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

// §25.10 (printed page 806) with §6.18: the type the typedef `item` written in
// the module `decl` takes from an interface through its port, `typedef
// i.choice yes_no;`: the interface's own typedef of that name, where the port
// `i` is declared of an interface `find_module` knows. Null where the port is
// generic, `interface i`, naming no interface until it is connected, where no
// port of `decl` has the name, or where the interface declares no such type.
const DataType* InterfacePortTypedefType(
    const ModuleItem* item, const ModuleDecl* decl,
    const std::function<const ModuleDecl*(std::string_view)>& find_module);

}  // namespace delta
