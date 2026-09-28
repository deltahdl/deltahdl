#include "simulator/eval_array_element_assoc.h"

#include <cstdint>
#include <map>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/assoc_element.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context_types.h"

namespace delta {

namespace {

// The entries of an associative array under one kind of key, `data`, and the
// array each element that is an associative array holds under the same key,
// `assocs`.
template <typename Key>
struct KeyedAssocs {
  std::map<Key, Logic4Vec>& data;
  std::map<Key, AssocArrayObject*>& assocs;
};

// The array under `key` of `outer`, whose entries under that kind of key are
// `entries`. A key the entries lack is allocated where `allocate` says so,
// the array a deleted entry left under it dropped so the new element starts
// empty (§7.8.7); read alone, it answers a fresh empty array and allocates
// nothing.
template <typename Key>
AssocArrayObject* ElementAssoc(AssocArrayObject* outer,
                               KeyedAssocs<Key> entries, const Key& key,
                               bool allocate, Arena& arena) {
  if (entries.data.count(key) == 0) {
    if (!allocate) return arena.Create<AssocArrayObject>(*outer->element_assoc);
    entries.data.emplace(key, AssocAllocValue(outer, arena));
    entries.assocs.erase(key);
  }
  AssocArrayObject*& inner = entries.assocs[key];
  if (inner == nullptr)
    inner = arena.Create<AssocArrayObject>(*outer->element_assoc);
  return inner;
}

}  // namespace

AssocArrayObject* ElementAssocOfSelect(const Expr* sel, SimContext& ctx,
                                       Arena& arena, bool allocate) {
  if (sel == nullptr || sel->kind != ExprKind::kSelect ||
      sel->base == nullptr || sel->index == nullptr ||
      sel->index_end != nullptr) {
    return nullptr;
  }
  AssocArrayObject* outer = FindAssocArrayOfBase(sel->base, ctx, arena);
  if (outer == nullptr || outer->element_assoc == nullptr) return nullptr;
  Logic4Vec idx = EvalExpr(sel->index, ctx, arena);
  if (outer->is_string_key) {
    return ElementAssoc(
        outer,
        KeyedAssocs<std::string>{outer->str_data, outer->str_element_assocs},
        AssocStringKey(idx), allocate, arena);
  }
  if (HasUnknownBits(idx)) return nullptr;
  int64_t key = AssocIntKey(idx, outer->is_wildcard, outer->index_width,
                            outer->is_index_signed);
  return ElementAssoc(
      outer, KeyedAssocs<int64_t>{outer->int_data, outer->int_element_assocs},
      key, allocate, arena);
}

}  // namespace delta
