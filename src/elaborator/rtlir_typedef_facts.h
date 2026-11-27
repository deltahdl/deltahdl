#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_map>

#include "common/packed_range.h"
#include "parser/ast_type.h"

namespace delta {

struct RtlirTypeParamFacts {
  std::string_view name;
  uint32_t width = 0;
  DataTypeKind kind = DataTypeKind::kNamed;
  bool is_signed = false;
  std::optional<PackedRange> range;
};

struct RtlirTypedefFacts {
  std::unordered_map<std::string_view, uint32_t> type_widths;
  std::unordered_map<std::string_view, DataTypeKind> type_kinds;
  std::unordered_map<std::string_view, bool> type_signed;
  std::unordered_map<std::string_view, const DataType*> type_layouts;
  std::unordered_map<std::string_view, const DataType*> type_enums;
  std::unordered_map<std::string_view, PackedRange> type_ranges;
  std::unordered_map<std::string_view, std::string_view> type_targets;
  std::unordered_map<std::string_view, std::string_view> type_interfaces;
};

}  // namespace delta
