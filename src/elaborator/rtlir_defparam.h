#pragma once

#include <string>

namespace delta {

struct Expr;
struct RtlirModule;

struct RtlirDefparam {
  const RtlirModule* target_module = nullptr;
  std::string target_name;
  const Expr* rhs = nullptr;
};

}  // namespace delta
