#pragma once

#include <cstdint>
#include <string>
#include <vector>

namespace delta {

struct Expr;

struct VpiExprScope {
  const Expr* expr = nullptr;
  std::string inst_prefix;
  std::vector<std::string> gen_prefixes;
  uint32_t context_width = 0;
};

}  // namespace delta
