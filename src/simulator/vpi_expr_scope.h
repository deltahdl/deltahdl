#pragma once

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
};

}  // namespace delta
