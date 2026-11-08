#pragma once

#include <string_view>
#include <unordered_set>

#include "parser/ast_module.h"

namespace delta {

bool BodyRefersOutsideInterface(
    const ModuleDecl* iface, const std::unordered_set<std::string_view>& local);

}  // namespace delta
