#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

class Arena;
struct ClassArrayRef;
struct Expr;
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
