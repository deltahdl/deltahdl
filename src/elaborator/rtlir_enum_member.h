#pragma once

#include <cstdint>
#include <string_view>

namespace delta {

struct DataType;
struct Expr;

struct RtlirEnumMember {
  std::string_view name;
  int64_t value = 0;
  const Expr* xz_value = nullptr;
  const DataType* enumeration = nullptr;
  std::string_view gen_block_prefix = {};
};

}  // namespace delta
