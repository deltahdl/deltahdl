#pragma once

#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

struct ArrayInfo;
struct Expr;
class SimContext;
class Arena;

// Shared between eval_array.cpp and eval_array_locator.cpp. Defined once in
// eval_array.cpp.
std::vector<Logic4Vec> CollectVecElements(std::string_view var_name,
                                          const ArrayInfo& info,
                                          SimContext& ctx, Arena& arena);

// The iterator-argument names parsed from an array method call's optional
// `with` clause arguments: the item name (default "item"), the index name
// (default "index"), and the synthesized "<item>.<index>" variable name.
struct IterNames {
  std::string_view iter_name;
  std::string_view index_name;
  std::string idx_var_name;
};

// Extracts the iterator/index argument names from `expr`, applying the default
// "item"/"index" names when an argument is absent or not an identifier. Defined
// once in eval_array.cpp; also used by eval_array_locator.cpp.
IterNames ExtractIterNames(const Expr* expr);

}  // namespace delta
