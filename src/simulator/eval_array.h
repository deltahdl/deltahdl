#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

struct Expr;
struct ArrayInfo;
struct AssocArrayObject;
struct QueueObject;
class SimContext;
class Arena;

// The notification a write to an aggregate's contents owes §9.4.2, which puts
// the duty on the writer: "Changing the value of object data members, aggregate
// elements, or the size of a dynamically sized array referenced by a method or
// function shall cause the event expression to be reevaluated". A queue, a
// dynamic array and an associative array all keep their elements outside the
// Variable registered under the aggregate's name, so a write that changes one
// leaves that variable's `value` standing still while the watchers armed on the
// name -- which is what a `wait (q[0] == 3)`, an `always_comb` reading `q[1]`
// and an `@(q[1])` all arm on -- have nothing else to go on. Every mutating
// queue method calls this; so does the indexed element write beside them.
// Defined in eval_array_queue.cpp.
void NotifyOwningVar(SimContext& ctx, std::string_view var_name);

bool TryEvalArrayMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out);

// Applies a §7.12.3 reduction whose with clause is attached to a bare
// member-access node (arr.sum with (e), the parenthesis-free LRM form). Returns
// false for anything that is not such a reduction so the caller continues with
// ordinary member resolution.
bool TryEvalArrayReductionWithClause(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out);

// Applies a §7.12.2 sort()/rsort() with-clause ordering key when the ordering
// call reaches evaluation as a bare member-access node: the parenthesis-free
// form (a.sort with (e), the LRM's own syntax) and every queue receiver, which
// the call-form executor does not cover. Reorders the array or queue in place
// and returns true; returns false for anything that is not such an ordering
// call so the caller falls back to ordinary member resolution.
bool TryExecArrayOrderingWithClauseStmt(const Expr* expr, SimContext& ctx,
                                        Arena& arena);

bool TryExecArrayMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena);

bool TryEvalArrayProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out);

bool TryExecArrayPropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena& arena);

bool TryEvalQueueMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out);
bool TryExecQueueMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena);
bool TryEvalQueueProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out);
bool TryExecQueuePropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena& arena);

bool TryEvalAssocMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out);
bool TryExecAssocMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena);
bool TryEvalAssocProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out);
bool TryExecAssocPropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena& arena);

// §12.7.3: the index values a foreach loop over the associative array `aa`
// steps through, in the array's own order -- §7.8.2's lexicographical order of
// string keys, each as the string value, and §7.8.4's numerical order of
// integral keys, each at the index type's width. Defined in
// eval_array_assoc.cpp, beside the traversal methods that hand out the same
// values one at a time.
std::vector<Logic4Vec> AssocIndexValues(const AssocArrayObject* aa,
                                        Arena& arena);

bool TryCollectLocatorResult(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::vector<Logic4Vec>& out);

// §7.12.1 with §7.4.4: the elements a locator that returns elements selects
// of an array whose elements are arrays -- the subarrays of a
// multidimensional fixed-size array, which `array_name` and `info` describe,
// or the elements
// of a queue or dynamic array whose elements are queues or fixed-size arrays,
// `queue` -- and the offset of each selected one into the array, in the order
// the locator returns them.
struct LocatorRows {
  std::string_view array_name;
  const ArrayInfo* info = nullptr;
  const QueueObject* queue = nullptr;
  std::vector<uint32_t> offsets;
};

// The elements `expr`, a call of find, find_first, find_last, min, max or
// unique on such an array, selects, in `out`. False where `expr` is no such
// call. Defined in eval_array_locator.cpp.
bool TryCollectLocatorRows(const Expr* expr, SimContext& ctx, Arena& arena,
                           LocatorRows& out);

bool TryCollectAssocMapResult(const Expr* expr, SimContext& ctx, Arena& arena,
                              AssocArrayObject& out);

// §11.4.13 with §7.10 and §7.8: the values of the queue or dynamic array, or
// of the associative array in index order, that `name` names, appended to
// `out`, each a member of an `inside` set. False, with `out` left alone, where
// `name` names none of them.
bool CollectQueueOrAssocValues(std::string_view name, SimContext& ctx,
                               std::vector<Logic4Vec>& out);

}  // namespace delta
