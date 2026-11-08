#pragma once

#include <functional>
#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

void CheckViModportsMatch(
    std::string_view lhs_name, std::string_view rhs_modport,
    const std::unordered_map<std::string_view, std::string_view>&
        vi_var_modports,
    SourceLoc loc, DiagEngine& diag);

struct ViInstanceModportTables {
  const std::unordered_map<std::string_view, std::string_view>&
      interface_inst_types;
  const std::unordered_map<std::string_view, std::string_view>& vi_var_modports;
  const std::function<const ModuleDecl*(std::string_view)>& find_module;
};

void CheckViFromInstanceModport(const Expr* lhs, const Expr* rhs,
                                const ViInstanceModportTables& tables,
                                SourceLoc loc, DiagEngine& diag);

}  // namespace delta
