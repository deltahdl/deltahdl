#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

// §23.10 / Syntax A.1.3 parameter_port_list: the collections being built up as
// each parameter_declaration / type_parameter_declaration in the list is
// parsed. It is the one accumulator for the whole parameter port list, so the
// value- and type-parameter parsers share it, and a module, interface, program
// or class header builds it over the declaration the header opens.
struct ParamPortList {
  std::vector<std::pair<std::string_view, Expr*>>& params;
  std::unordered_set<std::string_view>& type_param_names;
  std::unordered_set<std::string_view>& localparam_port_names;
  std::vector<DataType>* param_types;
  // Where a value parameter's unpacked dimensions go, by name.
  std::unordered_map<std::string_view, std::vector<Expr*>>* unpacked_dims;
  // Where each parameter's identifier was written, one per entry of `params`
  // in its order, for a header whose declaration keeps them; null for one
  // that does not.
  std::vector<SourceLoc>* locs = nullptr;
};

}  // namespace delta
