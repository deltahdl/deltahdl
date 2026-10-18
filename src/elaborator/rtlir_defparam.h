#pragma once

#include <string>

namespace delta {

struct Expr;
struct RtlirModule;

// §23.10.1: one assignment of a defparam statement that changed a parameter:
// the instance the parameter belongs to, the name that instance keys it under
// (a generate block's prefix ahead of its own name), and the right-hand side as
// written. Kept apart from rtlir.h, which stands near the size the
// assert-no-oversized-source-files job fails at.
struct RtlirDefparam {
  const RtlirModule* target_module = nullptr;
  std::string target_name;
  const Expr* rhs = nullptr;
};

}  // namespace delta
