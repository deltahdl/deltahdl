#pragma once

#include <functional>
#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

// §25.9 (printed page 801): the modport a source of an assignment to the
// virtual interface `lhs_name` selects, `rhs_modport`, empty for none, held to
// the modport the virtual interface selects (`vi_var_modports`). A modport
// selected is part of the type, so a source selecting one goes only to a
// virtual interface selecting the same; a source selecting none goes to any.
void CheckViModportsMatch(
    std::string_view lhs_name, std::string_view rhs_modport,
    const std::unordered_map<std::string_view, std::string_view>&
        vi_var_modports,
    SourceLoc loc, DiagEngine& diag);

// What CheckViFromInstanceModport reads: the module's interface instances
// with their interfaces, its virtual interfaces with the modports they select,
// and a lookup of an interface by its name.
struct ViInstanceModportTables {
  const std::unordered_map<std::string_view, std::string_view>&
      interface_inst_types;
  const std::unordered_map<std::string_view, std::string_view>& vi_var_modports;
  const std::function<const ModuleDecl*(std::string_view)>& find_module;
};

// §25.9: an assignment to the virtual interface `lhs` of `rhs`, where `rhs`
// names a modport of an interface instance, `p32.phy`, which selects that
// modport as a virtual interface selecting it would.
void CheckViFromInstanceModport(const Expr* lhs, const Expr* rhs,
                                const ViInstanceModportTables& tables,
                                SourceLoc loc, DiagEngine& diag);

}  // namespace delta
