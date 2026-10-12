#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

class Arena;
struct AssocArrayObject;
struct ClassArrayRef;
struct Expr;
struct QueueObject;
class SimContext;
struct Stmt;
struct StructFieldInfo;
struct Variable;

// §12.7.3: the name the array of a foreach loop is written as, a member path
// spelled with its dots; empty for any other expression.
std::string GetForeachArrayName(const Expr* expr);

// §12.7.3: one dimension a foreach loop variable walks, from the dimension's
// declared left bound to its right bound, counting down where the left bound is
// the higher. `var` is the loop variable that names it.
struct ForeachDim {
  std::string_view var;
  int64_t left = 0;
  bool descending = false;
  uint64_t size = 0;

  // The index the loop variable takes at position `pos` of the walk.
  int64_t IndexAt(uint64_t pos) const {
    auto step = static_cast<int64_t>(pos);
    return descending ? left - step : left + step;
  }
};

// §12.7.3 maps the loop variables of `stmt` to the dimensions of the array it
// names in dimension order, the unpacked dimensions first and then the packed
// ones (§7.4.5), and walks each named one from its left bound. These are the
// dimensions named with a variable, outermost first, of a declared fixed-size
// array or a declared vector: the unpacked dimensions as declared, then those
// of the element's packed type. A position the list skips is not walked and
// contributes nothing. Empty where `stmt` names no variable, or names anything
// else: a string, a queue, a dynamic or associative array, an array whose
// elements are queues, or a name with no declared variable.
std::vector<ForeachDim> DeclaredForeachDims(const Stmt* stmt, SimContext& ctx);

// §12.7.3: the number of iterations a foreach over the array or variable
// `name` runs, where the walk has one dimension: the array's element count,
// a string's character count, or another variable's bit width. Zero for a name
// no array or variable has.
uint32_t ForeachArraySize(std::string_view name, SimContext& ctx);

// §12.7.3 with §7.4, §7.8 and §7.10: the second loop variable of a foreach
// over a queue, dynamic array or associative array whose elements are queues
// or fixed-size arrays, `foreach (r[k, j])` over `int r[$][2]`, steps through
// the indices of the element the first names, which is its own queue. `var`
// is that variable, an int, null where the loop names none or the array's
// elements are no queues; `queue` or `assoc` the array.
struct ForeachElementDim {
  Variable* var = nullptr;
  const QueueObject* queue = nullptr;
  const AssocArrayObject* assoc = nullptr;
};

// The second dimension of the foreach `stmt`, whose array is the associative
// array `aa`, or a queue where `aa` is null; the loop variable is created in
// the scope the caller pushed.
ForeachElementDim ForeachElementDimOf(const Stmt* stmt,
                                      const AssocArrayObject* aa,
                                      SimContext& ctx, Arena& arena);

// The queue of the element the outer loop's iteration `i` names, whose index
// is `keys[i]` for an associative array.
const QueueObject* ForeachElementQueue(const ForeachElementDim& dim,
                                       const std::vector<Logic4Vec>& keys,
                                       uint32_t i, Arena& arena);

// The value the second loop variable takes at position `p` of the element
// queue `element`: a fixed-size element's declared index from its left bound,
// a queue's position itself, as an int.
Logic4Vec ForeachElementIndex(const QueueObject& element, uint32_t p,
                              Arena& arena);

// §12.7.3 with §7.4.2 and §8.5: the named dimensions of the array property
// `ref` names as a whole, which `stmt` walks. A property with one unpacked
// dimension is walked from its declared left bound, a dynamic one from 0, and
// so is each dimension of a property with more than one, `foreach (h.g[i, j])`
// over `int g[2][3]`. Empty where `ref` is a subarray of the property.
std::vector<ForeachDim> ClassArrayForeachDims(const Stmt* stmt,
                                              const ClassArrayRef& ref);

// §12.7.3 with §7.2: the dimension of the unpacked array member of a
// structure `member` describes, walked from its declared left bound, where
// `stmt` names its loop variable.
std::vector<ForeachDim> StructMemberForeachDims(const Stmt* stmt,
                                                const StructFieldInfo& member);

// How many sets of loop-variable values the nested walk of `dims` visits.
uint64_t ForeachCombinationCount(const std::vector<ForeachDim>& dims);

// Creates the loop variable of each of `dims` in the innermost scope, which
// the caller has pushed.
std::vector<Variable*> CreateForeachDimVars(const std::vector<ForeachDim>& dims,
                                            SimContext& ctx);

// Gives `vars` the values of set `n` of the walk, counted as nested loops
// count them: the last dimension varies fastest and the first most slowly.
void SetForeachDimVars(const std::vector<ForeachDim>& dims,
                       const std::vector<Variable*>& vars, uint64_t n,
                       Arena& arena);

}  // namespace delta
