#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

struct ArrayInfo;
struct AssocArrayObject;
struct Expr;
struct QueueObject;
class SimContext;
class Arena;

// Shared between eval_array.cpp and eval_array_locator.cpp. Defined once in
// eval_array.cpp.
std::vector<Logic4Vec> CollectVecElements(std::string_view var_name,
                                          const ArrayInfo& info,
                                          SimContext& ctx, Arena& arena);

// Flattens the associative array into parallel key/value vectors in
// ascending-key order, the first()/last() ordering of §7.9: an integral key
// at the index width with the index type's signedness, a string key as its
// text (§7.8.1), which std::map orders lexicographically as §7.9 does. Each
// value reads with the element type's signedness (§6.11). Defined in
// eval_array_locator.cpp; also used by the reductions in eval_array.cpp.
void CollectAssocKeyVals(const AssocArrayObject& aa, Arena& arena,
                         std::vector<Logic4Vec>& keys,
                         std::vector<Logic4Vec>& vals);

// §7.12 with §6.16: whether the fixed-size or dynamic array `var_name`
// describes by `info` holds strings, by its declared element type or, where
// that was not recorded, by the string registration of the array or its first
// element. Defined in eval_array_locator.cpp.
bool IsStringArray(std::string_view var_name, const ArrayInfo& info,
                   SimContext& ctx);

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

// §7.4.4 with §7.12: whether `info` describes a fixed-size array of more than
// one unpacked dimension, whose elements are subarrays rather than values.
// Defined in eval_array_subarray.cpp, as is BindSubarrayIterator.
bool HasSubarrayElements(const ArrayInfo& info);

// §7.4.4: one element of a multidimensional array, a subarray: the element
// `offset` places into the first dimension of the array `array_name` that
// `info` describes.
struct SubarrayElement {
  std::string_view array_name;
  const ArrayInfo& info;
  uint32_t offset;
};

// §7.12 with §7.4.4: binds the iterator `iter_name` of a with clause, in the
// current scope, to `element` as the subarray it is: registered as an array
// of the remaining dimensions, its elements local copies of that element's
// own, so that `item.sum with (item)` and `item[1]` read it.
void BindSubarrayIterator(const SubarrayElement& element,
                          std::string_view iter_name, SimContext& ctx,
                          Arena& arena);

// §7.4.4: `sel`, a select of one or more leading dimensions of a
// multidimensional fixed-size array, `m2[1]` or `m3[1][0]`, names a subarray,
// itself an unpacked array: `prefix` receives the name its elements' variables
// begin with, "m2[1]", and `sub` the dimensions left, so the array paths that
// read an array by name and ArrayInfo read it. False where `sel` names no
// subarray, an index holding an x or z bit or outside its dimension included.
// Defined in eval_array_subarray.cpp.
bool ResolveSubarraySelect(const Expr* sel, SimContext& ctx, Arena& arena,
                           std::string& prefix, ArrayInfo& sub);

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

// §7.12.3: `vals` folded by the reduction `method` names -- sum, product, and,
// or or xor -- and 0 for any other name. Defined in eval_array_value_ops.cpp.
uint64_t ApplyReduction(std::string_view method,
                        const std::vector<uint64_t>& vals);

// §7.12.1 and §7.12.2 with §6.11: whether `a` comes before `b` in the order
// min(), max(), sort() and rsort() put two values of one integral type in --
// as two's-complement numbers where `is_signed` says that type is signed, and
// as unsigned ones where it is not. Defined in eval_array_value_ops.cpp.
bool OrdersBefore(const Logic4Vec& a, const Logic4Vec& b, bool is_signed);

// Defined in eval_array.cpp; §7.12.2: the queue `q` sorted by the value the
// with clause of `expr` gives each element, ascending or descending, its
// element ids following their elements (§7.10.3).
void SortQueueByWithExpr(QueueObject* q, const Expr* expr, bool ascending,
                         SimContext& ctx, Arena& arena);

}  // namespace delta
