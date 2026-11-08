#pragma once

#include <string_view>

#include "parser/ast_stmt.h"

namespace delta {

struct ProceduralCheckerSite {
  const Stmt* stmt = nullptr;
  std::string_view inst_name;
};

}  // namespace delta
