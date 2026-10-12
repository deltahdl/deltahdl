#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/pattern_type_key.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

namespace {
// §7.4.2: bundle for materializing the leaves of a fixed multidimensional
// unpacked array, keeping the recursive walk within the parameter-count limit;
// `in_place` writes each leaf already standing under its key rather than
// creating one (InitArrayElements).
struct MultiDimArray {
  const RtlirVariable& var;
  SimContext& ctx;
  Arena& arena;
  bool in_place = false;
};
}  // namespace

// §10.9.1: array assignment patterns can use a form like replication too, each
// replication standing for one whole dimension. A replicated item is therefore
// not one element's value but the body of the dimension it stands for, cycled
// across that dimension's positions -- which is what makes the clause's own
// `'{2{'{3{y}}}}` the same as `'{'{y,y,y},'{y,y,y}}`. Null when this pattern is
// not the replicated form.
static const std::vector<Expr*>* ReplicateBody(const Expr* pat) {
  if (!pat->pattern_keys.empty()) return nullptr;
  if (pat->elements.size() != 1) return nullptr;
  if (!pat->elements[0]->is_pattern_replication) return nullptr;
  const auto& body = pat->elements[0]->elements;
  return body.empty() ? nullptr : &body;
}

// §10.9.1: the braces follow the array's dimensions, so an item that is
// itself a brace pattern is the sub-pattern of the next dimension in.
static bool IsDimPattern(const Expr* item) {
  return item->kind == ExprKind::kAssignmentPattern ||
         item->kind == ExprKind::kConcatenation;
}

// §10.9: only a brace pattern matches the array's dimensions, so only one is
// distributed into the leaves; a typed assignment pattern expression
// (`T'{...}`) parses as a cast wrapping one, so unwrap that first. Null for a
// declaration with no initializer, or one whose initializer is not a pattern at
// all.
static const Expr* ArrayInitPattern(const Expr* init) {
  if (!init) return nullptr;
  if (init->kind == ExprKind::kCast && init->lhs && IsDimPattern(init->lhs))
    return init->lhs;
  return IsDimPattern(init) ? init : nullptr;
}

// §10.9.1's three matching rules for one element of a multidimensional array,
// asked in the order the clause writes them: index key, then type key, then
// default. Null when none of them covers the element -- which the clause
// forbids, requiring one of the rules to cover every element.
static const Expr* FindKeyedItem(const Expr* pat, uint32_t idx,
                                 const MultiDimArray& m) {
  if (const Expr* item = IndexKeyedItem(pat, idx, m.ctx, m.arena)) return item;
  if (const Expr* item = TypeKeyedItem(
          pat, SubjectOfVariableElement(m.var, m.ctx, m.arena), m.ctx))
    return item;
  return DefaultKeyedItem(pat);
}

// §10.9.1: the item of `pat` that fills one dimension's element at address
// `idx`, position `pos` within that dimension. All three item forms the clause
// admits are read here -- keyed, replicated, and positional -- so the descent
// below meets the same three the single-dimension maker does. Null when the
// pattern supplies nothing for this element.
static const Expr* SelectDimItem(const Expr* pat, uint32_t idx, uint32_t pos,
                                 const MultiDimArray& m) {
  if (!pat->pattern_keys.empty()) return FindKeyedItem(pat, idx, m);
  if (const auto* body = ReplicateBody(pat)) return (*body)[pos % body->size()];
  return pos < pat->elements.size() ? pat->elements[pos] : nullptr;
}

// Materializes one leaf variable of the array under `name`, a variable of
// the array's element type: its state-ness and signedness are the
// declaration's (§6.11.2, §6.11.3), and its index resolves as the
// declaration's packed dimension says (§11.5.1).
static Variable* NewMultiDimLeaf(const MultiDimArray& m,
                                 const std::string& name) {
  auto* stored = m.arena.Create<std::string>(name);
  auto* elem = m.ctx.CreateVariable(*stored, m.var.width);
  RecordPackedRange(m.var.dtype, elem, m.ctx, m.arena);
  elem->is_4state = m.var.is_4state;
  elem->is_signed = m.var.is_signed;
  elem->is_string = m.var.is_string;
  return elem;
}

Variable* ExistingArrayElement(SimContext& ctx, const std::string& key) {
  const auto& variables = ctx.GetVariables();
  auto found = variables.find(key);
  return found == variables.end() ? nullptr : found->second;
}

// The leaf of the array under `name`: the one made here, or the one already
// standing under its key for a walk in place.
static Variable* MultiDimLeaf(const MultiDimArray& m, const std::string& name) {
  return m.in_place ? ExistingArrayElement(m.ctx, name)
                    : NewMultiDimLeaf(m, name);
}

// §10.9.1: each expression item is evaluated as though assigned to the type
// of its element, so the value is coerced to the element width (a no-op when
// they already match). §6.8 then makes the leaf a data object that stores a
// value of its own, so it takes its own words: a bare item name of the leaf's
// width is answered with that variable's Logic4Vec, ResizeToWidth hands it
// straight back, and without the copy every leaf of `'{2{'{3{y}}}}` would
// share y's storage.
static void StoreMultiDimLeaf(const MultiDimArray& m, const std::string& name,
                              const Logic4Vec& val) {
  Variable* elem = MultiDimLeaf(m, name);
  if (elem == nullptr) return;
  elem->value = OwnRhsWords(ResizeToWidth(val, m.var.width, m.arena), m.arena);
}

// Gives one leaf variable of the array the value of the pattern item that
// reached it, or §6.8 Table 6-7's default when none did.
static void CreateMultiDimLeaf(const MultiDimArray& m, const std::string& name,
                               const Expr* item) {
  if (item != nullptr) {
    StoreMultiDimLeaf(m, name, EvalExpr(item, m.ctx, m.arena));
    return;
  }
  // §6.8, Table 6-7: nothing covered this leaf, so it keeps the default
  // initial value of its type -- the 'x CreateVariable seeded for a 4-state
  // element (masked to the width there, which MakeAllX does not do), and '0
  // for a 2-state one. Exactly what an uncovered leaf held before this walk
  // carried an initializer at all.
  Variable* elem = MultiDimLeaf(m, name);
  if (elem != nullptr && !m.var.is_4state)
    elem->value = MakeLogic4VecVal(m.arena, m.var.width, 0);
}

// An element is named by its index's 32 bits, as every select names it
// (TryArrayElementSelect, BuildCompoundName) and ArrayElementKey names a
// one-dimensional array's, so `[-1:0]` holds [4294967295] and [0].
static std::string MultiDimChildName(const std::string& prefix, int64_t idx) {
  return prefix + "[" + std::to_string(static_cast<uint32_t>(idx)) + "]";
}

// §11.5.2 counts an address from the smaller of the two bounds the
// declaration wrote, whichever way round it wrote them, while §10.9.1 counts a
// pattern's positional items, and §7.6 an unpacked array's elements, from the
// dimension's left bound. A descending dimension therefore takes them the
// other way round, exactly as the single-dimension maker's pat_idx does: `k`
// counted from the one end is this, counted from the other. is_descending on
// the variable describes only the first dimension, so each dimension is asked
// its own bounds instead.
static uint32_t FromLeftBound(const MultiDimArray& m, size_t d, uint32_t k) {
  const auto& dim = m.var.unpacked_dims[d];
  return dim.left > dim.right ? m.var.unpacked_dim_sizes[d] - 1 - k : k;
}

// §7.4.4: the number of leaves beneath dimension `d`.
static size_t MultiDimLeafCount(const MultiDimArray& m, size_t d) {
  size_t count = 1;
  for (size_t k = d; k < m.var.unpacked_dim_sizes.size(); ++k)
    count *= m.var.unpacked_dim_sizes[k];
  return count;
}

// §7.6: the leaves beneath dimension `d` of the subarray under `prefix` take
// `elems` in turn, by left-to-right position, from `next` on.
static void StoreSubarrayLeaves(const MultiDimArray& m,
                                const std::string& prefix, size_t d,
                                const std::vector<Logic4Vec>& elems,
                                size_t& next) {
  if (d == m.var.unpacked_dim_sizes.size()) {
    StoreMultiDimLeaf(m, prefix, elems[next++]);
    return;
  }
  for (uint32_t pos = 0; pos < m.var.unpacked_dim_sizes[d]; ++pos) {
    int64_t idx = m.var.unpacked_dims[d].Low() + FromLeftBound(m, d, pos);
    StoreSubarrayLeaves(m, MultiDimChildName(prefix, idx), d + 1, elems, next);
  }
}

static void CreateMultiDimLeaves(const MultiDimArray& m,
                                 const std::string& prefix, size_t d,
                                 const Expr* item);

// §10.9.1 with §7.6: an item standing for the subarray beneath dimension `d`
// that is itself an unpacked array -- a variable or queue named whole, a
// slice, or a select of another array's leading dimensions -- is assigned to
// that subarray as one unpacked array to another, its elements paired with
// the subarray's leaves by left-to-right position. One of another size is
// reported, and its subarray keeps §6.8 Table 6-7's default. False for an item
// that is no unpacked array, which the clause applies to every leaf beneath.
static bool CreateLeavesFromArrayItem(const MultiDimArray& m,
                                      const std::string& prefix, size_t d,
                                      const Expr* item) {
  std::vector<Logic4Vec> elems;
  if (!CollectArrayItemElements(item, m.ctx, m.arena, elems)) return false;
  if (elems.size() != MultiDimLeafCount(m, d)) {
    m.ctx.GetDiag().Error(
        item->range.start,
        "array size mismatch in assignment to fixed-size array",
        Subclause("7.6"));
    CreateMultiDimLeaves(m, prefix, d, nullptr);
    return true;
  }
  size_t next = 0;
  StoreSubarrayLeaves(m, prefix, d, elems, next);
  return true;
}

// §10.9.1: the sub-pattern an item standing at a dimension other than the last
// gives that dimension -- a brace pattern, or one typed as an unpacked array
// (`row_t'{4, 5, 6}`), which is that subarray's own pattern. Null for any
// other item.
static const Expr* SubarrayPattern(const Expr* item, SimContext& ctx) {
  if (item == nullptr) return nullptr;
  if (IsDimPattern(item)) return item;
  return TypedUnpackedArrayPattern(item, ctx);
}

// §7.4.2: recursively create one leaf variable per element of a fixed
// multidimensional unpacked array, named arr[i0][i1]... in row-major order so a
// compound select (eval_select.cpp) and a nested assignment pattern resolve to
// it. `item` is the part of the declaration initializer that reached this
// subtree: §10.9.1 has the braces follow the array's dimensions, so the
// initializer is a tree of the array's own shape and the walk carries the
// sub-pattern for the current dimension down beside the prefix it already
// carried. This is the step the two makers of array leaves differed by -- the
// single-dimension one applied the initializer and this one never read it, so
// the clause's own `int n[1:2][1:3] = '{2{'{3{y}}}};` read 0 at all six leaves.
// A leaf no item reaches keeps §6.8 Table 6-7's default, unchanged.
static void CreateMultiDimLeaves(const MultiDimArray& m,
                                 const std::string& prefix, size_t d,
                                 const Expr* item) {
  const auto& sizes = m.var.unpacked_dim_sizes;
  if (d == sizes.size()) {
    CreateMultiDimLeaf(m, prefix, item);
    return;
  }
  const Expr* pat = SubarrayPattern(item, m.ctx);
  if (pat == nullptr && item != nullptr &&
      CreateLeavesFromArrayItem(m, prefix, d, item))
    return;
  for (uint32_t i = 0; i < sizes[d]; ++i) {
    int64_t idx = m.var.unpacked_dims[d].Low() + i;
    // A value of no aggregate type standing where this dimension's braces
    // were expected is what a type or default key resolves to for a whole
    // subarray, and the clause applies it recursively, so it passes down
    // unchanged to every leaf beneath.
    const Expr* sub = pat ? SelectDimItem(pat, static_cast<uint32_t>(idx),
                                          FromLeftBound(m, d, i), m)
                          : item;
    CreateMultiDimLeaves(m, MultiDimChildName(prefix, idx), d + 1, sub);
  }
}

void FillMultiDimLeaves(std::string_view name, const RtlirVariable& var,
                        SimContext& ctx, Arena& arena, bool in_place) {
  CreateMultiDimLeaves(MultiDimArray{var, ctx, arena, in_place},
                       std::string(name), 0, ArrayInitPattern(var.init_expr));
}

}  // namespace delta
