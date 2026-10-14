#pragma once

#include <string_view>
#include <unordered_set>

#include "parser/ast_module.h"

namespace delta {

// §25.9 (printed page 801): whether a procedural body of the interface
// `iface`, a process's or a task's or a function's, refers by a hierarchical
// name to an object outside the interface: a dotted name whose first name the
// interface declares neither among its own names, `local`, nor in the body
// that holds it. A name written with `::` along it reaches a package or a
// class rather than the hierarchy, and is passed over.
bool BodyRefersOutsideInterface(
    const ModuleDecl* iface, const std::unordered_set<std::string_view>& local);

}  // namespace delta
