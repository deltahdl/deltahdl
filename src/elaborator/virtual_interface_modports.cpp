// §25.9: the modport a virtual interface selects, as part of its type, held
// to the modport the source of an assignment to it selects.

#include "elaborator/virtual_interface_modports.h"

#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_helpers.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

void CheckViModportsMatch(
    std::string_view lhs_name, std::string_view rhs_modport,
    const std::unordered_map<std::string_view, std::string_view>&
        vi_var_modports,
    SourceLoc loc, DiagEngine& diag) {
  if (rhs_modport.empty()) return;
  auto lmp = vi_var_modports.find(lhs_name);
  bool lhs_has_mp = lmp != vi_var_modports.end() && !lmp->second.empty();
  if (!lhs_has_mp) {
    diag.Error(loc,
               "virtual interface with modport cannot be assigned to "
               "virtual interface without modport",
               Subclause("25.9"));
  } else if (lmp->second != rhs_modport) {
    diag.Error(loc, "virtual interface modports do not match",
               Subclause("25.9"));
  }
}

void CheckViFromInstanceModport(const Expr* lhs, const Expr* rhs,
                                const ViInstanceModportTables& tables,
                                SourceLoc loc, DiagEngine& diag) {
  auto it = tables.interface_inst_types.find(ExprIdent(rhs->lhs));
  const ModuleDecl* iface = it == tables.interface_inst_types.end()
                                ? nullptr
                                : tables.find_module(it->second);
  if (iface == nullptr) return;
  std::string_view modport = rhs->rhs->text;
  for (const ModportDecl* mp : iface->modports) {
    if (mp->name != modport) continue;
    CheckViModportsMatch(ExprIdent(lhs), modport, tables.vi_var_modports, loc,
                         diag);
    return;
  }
}

}  // namespace delta
