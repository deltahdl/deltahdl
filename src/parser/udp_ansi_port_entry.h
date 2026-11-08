#pragma once

#include <string_view>

#include "common/source_loc.h"
#include "parser/ast_expr.h"

namespace delta {

struct UdpAnsiPortEntry {
  bool is_output = false;
  bool is_inout = false;
  bool declares_reg = false;
  bool keyword_omitted = false;
  Expr* initial_expr = nullptr;
  std::string_view name;
  SourceLoc loc;
};

}  // namespace delta
