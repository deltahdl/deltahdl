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

// What the elaborated tables record about each name a typedef declares: how
// wide the type it stands for is, what kind it is, and whether it is signed.
// They travel together because one walk of the typedef map fills all three and
// because a declaration reads them together.
struct TypeNameFacts {
  std::unordered_map<std::string_view, uint32_t>& widths;
  std::unordered_map<std::string_view, DataTypeKind>& kinds;
  std::unordered_map<std::string_view, bool>& is_signed;
  std::unordered_map<std::string_view, const DataType*>& layouts;
  std::unordered_map<std::string_view, std::string_view>& targets;
  std::unordered_map<std::string_view, PackedRange>& ranges;
  std::unordered_map<std::string_view, const DataType*>& enums;
};

// What the typedef table has to say about the names in it: the table itself,
// the names within it that stand for an aggregate, and the arena the resolved
// copies recorded from it are built in. Bundled because a fourth fact is now
// read off the same table and the three sources are one subject.
struct TypeNameSources {
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& aggregates;
  Arena& arena;
};

// §6.18: the facts recorded about every name the typedef table holds -- how
// wide, what kind, signed or not, the layout of a packed structure or union,
// the class at the end of a chain of typedefs, the packed range and the
// enumeration a name stands for -- each into the map of `out` that
// RtlirDesign carries it in. Defined in elaborator_type_facts.cpp, moved out
// of elaborator.cpp, which stood at the size the
// assert-no-oversized-source-files job fails at.
void PopulateTypeWidths(const TypeNameSources& src, TypeNameFacts& out);

}  // namespace delta
