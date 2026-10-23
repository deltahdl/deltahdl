#pragma once

#include <cstdint>
#include <string_view>

namespace delta {

struct DataType;
struct Expr;

// §6.19: one named constant of an enumeration, with the value it holds. Kept
// apart from rtlir.h, which stood at the size the
// assert-no-oversized-source-files job fails at.
struct RtlirEnumMember {
  std::string_view name;
  int64_t value = 0;
  // §6.19: the value expression of a member of a 4-state enumeration assigned
  // an x or z value, which `value` cannot hold; null for any other member.
  const Expr* xz_value = nullptr;
  // §6.19.3: the enumeration declaring this constant, as its declaration
  // wrote it, which a type reference to the constant stands for (§6.23).
  // Arena-owned with the declaration.
  const DataType* enumeration = nullptr;
};

}  // namespace delta
