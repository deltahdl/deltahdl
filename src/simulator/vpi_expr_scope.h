#pragma once

#include <cstdint>
#include <string>
#include <vector>

namespace delta {

struct Expr;

// §37.3.5 with §38.15: what vpi_get_value needs to give an expression object
// that holds no storage of its own its value -- the expression the source
// wrote, and the instance and generate-block prefixes its names resolve under,
// those a process running where it stands would carry.
struct VpiExprScope {
  const Expr* expr = nullptr;
  std::string inst_prefix;
  std::vector<std::string> gen_prefixes;
  // §11.6.1 with §10.7: the width of the left side a continuous assignment's
  // right-hand side is evaluated in the context of and sized to, the value the
  // assignment drives; 0 for an expression read at its own width.
  uint32_t context_width = 0;
};

}  // namespace delta
