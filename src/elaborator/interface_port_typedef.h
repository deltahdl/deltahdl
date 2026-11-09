#pragma once

#include <functional>
#include <string_view>

#include "parser/ast_module.h"

namespace delta {

const ModuleItem* InterfacePortTypedef(
    const ModuleItem* item, const ModuleDecl* decl,
    const std::function<const ModuleDecl*(std::string_view)>& find_module);

}  // namespace delta
