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

struct ParamPortList {
  std::vector<std::pair<std::string_view, Expr*>>& params;
  std::unordered_set<std::string_view>& type_param_names;
  std::unordered_set<std::string_view>& localparam_port_names;
  std::vector<DataType>* param_types;
  std::unordered_map<std::string_view, std::vector<Expr*>>* unpacked_dims;
  std::vector<SourceLoc>* locs = nullptr;
  std::unordered_map<std::string_view, DataTypeKind>* type_param_restrictions =
      nullptr;
};

}  // namespace delta
