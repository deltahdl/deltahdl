#pragma once

#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"
#include "parser/ast_module.h"

namespace delta {

// §25.7 (printed page 793): whether the subroutine prototype `proto` a modport
// writes matches the subroutine `body` exactly: the same kind, task or
// function, the same number of arguments with the same types and directions,
// and, for a function, the same return type.
bool PrototypeMatchesSubroutine(const ModuleItem* proto,
                                const ModuleItem* body);

// §25.7: checks the subroutine `port` of the modport `mp` of the interface
// `iface` imports. A full prototype shall match the interface's own
// declaration of the subroutine, with the formal names the prototype gives;
// importing by the identifier alone a subroutine the interface does not
// define, one another module defines, needs a full prototype.
void CheckModportImport(const ModuleDecl* iface, const ModportDecl* mp,
                        const ModportPort& port, DiagEngine& diag);

// The interface and the modport a port of a module selects in its header,
// `sb.mp p`.
struct SelectedModport {
  const ModuleDecl* iface;
  const ModportDecl* modport;
};
using SelectedModports = std::unordered_map<std::string_view, SelectedModport>;

// §25.7: checks each call `decl` makes through one of its ports `ports`
// names, `p.f(...)`, of a subroutine the port's modport imports. Through an
// import by the identifier alone a call may bind no argument by name and leave
// no argument to its default; through a full prototype, an argument the call
// leaves out takes the default the prototype gives it, written into the call,
// and is an error where the prototype gives none.
void CheckModportImportCalls(const ModuleDecl* decl,
                             const SelectedModports& ports, DiagEngine& diag);

}  // namespace delta
