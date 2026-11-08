#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "common/arena.h"
#include "common/packed_range.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

struct TypeNameFacts {
  std::unordered_map<std::string_view, uint32_t>& widths;
  std::unordered_map<std::string_view, DataTypeKind>& kinds;
  std::unordered_map<std::string_view, bool>& is_signed;
  std::unordered_map<std::string_view, const DataType*>& layouts;
  std::unordered_map<std::string_view, std::string_view>& targets;
  std::unordered_map<std::string_view, PackedRange>& ranges;
  std::unordered_map<std::string_view, const DataType*>& enums;
  std::unordered_map<std::string_view, std::string_view>& interfaces;
};

struct TypeNameSources {
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& aggregates;
  Arena& arena;
};

void PopulateTypeWidths(const TypeNameSources& src, TypeNameFacts& out);

}  // namespace delta
