#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/source_loc.h"

namespace delta {

struct Expr;

struct ResolvedAttribute {
  std::string_view name;
  std::optional<int64_t> resolved_value;
  std::string_view string_value;
  const Expr* value = nullptr;
  SourceLoc loc;
};

using RtlirNodeAttributes =
    std::unordered_map<const void*, std::vector<ResolvedAttribute>>;

}  // namespace delta
