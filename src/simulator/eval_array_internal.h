#pragma once

#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

struct ArrayInfo;
struct AssocArrayObject;
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

// §7.12 with §7.2: for as long as this lives, the iterator `iter_name` of a
// with clause over the array `array_name` is laid out by the structure type
// of the array's elements, so that `item.red` reads the member of the element
// the iterator holds; left as it was for an array of any other elements, and
// given back its own binding afterwards. Unbound, the iterator was a plain
// vector and every member of it read 0.
class IteratorLayout {
 public:
  IteratorLayout(std::string_view iter_name, std::string_view array_name,
                 SimContext& ctx);
  ~IteratorLayout();
  IteratorLayout(const IteratorLayout&) = delete;
  IteratorLayout& operator=(const IteratorLayout&) = delete;

 private:
  SimContext& ctx_;
  std::string_view iter_name_;
  std::string_view previous_;
  bool bound_ = false;
};

// §7.12.3: the array reduction methods over an associative array, which reach
// its elements by a route of their own rather than through ArrayInfo. Empty
// where `method` names no reduction, which is what lets a caller go on to try
// the §7.9 methods instead. Defined once in eval_array.cpp; also used by
// eval_array_assoc.cpp, since §7.9's num() and its method dispatch both have to
// offer the reductions first.
std::optional<Logic4Vec> TryAssocReduction(AssocArrayObject* aa,
                                           std::string_view method,
                                           const Expr* expr, SimContext& ctx,
                                           Arena& arena);

}  // namespace delta
