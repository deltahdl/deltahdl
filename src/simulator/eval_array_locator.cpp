#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_array_element_queue.h"
#include "simulator/eval_array_internal.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

bool IsStringArray(std::string_view var_name, const ArrayInfo& info,
                   SimContext& ctx) {
  // §7.12.1 with §6.16: an array declared of string elements holds strings,
  // which its with clause compares lexicographically, whatever its first
  // element's variable was registered as.
  if (info.elem_type_kind == DataTypeKind::kString) return true;
  if (info.is_dynamic) return ctx.IsStringVariable(var_name);
  auto name = std::string(var_name) + "[" + std::to_string(info.lo) + "]";
  return ctx.IsStringVariable(name);
}

static bool IsLocatorMethod(std::string_view name) {
  return name == "find" || name == "find_first" || name == "find_last" ||
         name == "find_index" || name == "find_first_index" ||
         name == "find_last_index" || name == "min" || name == "max" ||
         name == "unique" || name == "unique_index" || name == "map";
}

struct LocatorCtx {
  const std::vector<Logic4Vec>& elems;
  bool is_string;
  const Expr* with_expr;
  SimContext& ctx;
  Arena& arena;
  std::string_view iter_name = "item";
  std::string idx_var_name = "item.index";
  // §7.4.4: the multidimensional fixed-size array whose elements are the
  // subarrays the iterator is bound to, and its shape; null for an array
  // whose elements are values.
  std::string_view subarray_owner = {};
  const ArrayInfo* subarray_info = nullptr;
  // §7.10: the queue or dynamic array whose elements are queues or fixed-size
  // arrays, each of which the iterator is bound to; null for any other array.
  const QueueObject* element_queue_owner = nullptr;
  // §7.12.4 with §7.4.2: the index of the first element, a fixed-size array's
  // low bound, which every reported index and the index iterator count from.
  uint32_t index_base = 0;
  // §7.12.1 with §7.4.2: whether the array's range was declared from the high
  // index down, which puts its leftmost element at the end of `elems`.
  bool is_descending = false;
};

static LocatorCtx MakeLocatorCtx(const std::vector<Logic4Vec>& elems,
                                 bool is_str, const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  auto names = ExtractIterNames(expr);
  return LocatorCtx{elems,
                    is_str,
                    expr->with_expr,
                    ctx,
                    arena,
                    names.iter_name,
                    std::move(names.idx_var_name)};
}

// Pushes a fresh scope and binds the per-iteration locator iterators: the
// element iterator (item_val, optionally registered as a string, and signed
// where the element type is, §7.12 with §6.11, or the subarray at item_index
// of a multidimensional array, §7.4.4) and the index iterator (item_index,
// 32-bit). The caller is responsible for evaluating the with expression in
// this scope and calling PopScope afterwards.
static void SetupLocatorScope(const LocatorCtx& lc, const Logic4Vec& item_val,
                              size_t item_index) {
  lc.ctx.PushScope();
  if (lc.element_queue_owner != nullptr) {
    BindElementQueueIterator(*lc.element_queue_owner, item_index, lc.iter_name,
                             lc.ctx, lc.arena);
  } else if (lc.subarray_info != nullptr) {
    BindSubarrayIterator(SubarrayElement{lc.subarray_owner, *lc.subarray_info,
                                         static_cast<uint32_t>(item_index)},
                         lc.iter_name, lc.ctx, lc.arena);
  } else {
    auto* item_var = lc.ctx.CreateLocalVariable(lc.iter_name, item_val.width,
                                                item_val.is_signed);
    item_var->value = item_val;
    if (lc.is_string) lc.ctx.RegisterStringVariable(lc.iter_name);
  }
  auto* idx_var = lc.ctx.CreateLocalVariable(lc.idx_var_name, 32);
  idx_var->value = MakeLogic4VecVal(lc.arena, 32, lc.index_base + item_index);
}

static bool EvalLocatorPredicate(const LocatorCtx& lc,
                                 const Logic4Vec& item_val, size_t item_index) {
  SetupLocatorScope(lc, item_val, item_index);
  auto result = EvalExpr(lc.with_expr, lc.ctx, lc.arena).ToUint64();
  lc.ctx.PopScope();
  return result != 0;
}

static Logic4Vec EvalLocatorWithExpr(const LocatorCtx& lc,
                                     const Logic4Vec& item_val,
                                     size_t item_index) {
  SetupLocatorScope(lc, item_val, item_index);
  auto result = EvalExpr(lc.with_expr, lc.ctx, lc.arena);
  lc.ctx.PopScope();
  return result;
}

// §7.12.1: whether the first- or last-finding locator `method` scans from the
// highest index down. The first element is the one closest to the leftmost
// index and the last the one closest to the rightmost, which are the lowest
// and highest indices of an ascending range and the other way round for a
// descending one.
static bool ScansFromHighEnd(std::string_view method, const LocatorCtx& lc) {
  bool is_last = method == "find_last" || method == "find_last_index";
  return is_last != lc.is_descending;
}

static void LocatorFind(std::string_view method, const LocatorCtx& lc,
                        std::vector<Logic4Vec>& out) {
  for (size_t i = 0; i < lc.elems.size(); ++i) {
    if (!EvalLocatorPredicate(lc, lc.elems[i], i)) continue;
    out.push_back(lc.elems[i]);
    if (method == "find_first" || method == "find_last") break;
  }
}

static void LocatorFindDispatch(std::string_view method, const LocatorCtx& lc,
                                std::vector<Logic4Vec>& out) {
  if (method != "find" && ScansFromHighEnd(method, lc)) {
    for (size_t i = lc.elems.size(); i > 0; --i) {
      if (!EvalLocatorPredicate(lc, lc.elems[i - 1], i - 1)) continue;
      out.push_back(lc.elems[i - 1]);
      break;
    }
    return;
  }
  LocatorFind(method, lc, out);
}

static void LocatorFindIndex(std::string_view method, const LocatorCtx& lc,
                             std::vector<Logic4Vec>& out) {
  if (method != "find_index" && ScansFromHighEnd(method, lc)) {
    for (size_t i = lc.elems.size(); i > 0; --i) {
      if (!EvalLocatorPredicate(lc, lc.elems[i - 1], i - 1)) continue;
      out.push_back(MakeLogic4VecVal(lc.arena, 32, lc.index_base + i - 1));
      break;
    }
    return;
  }
  for (size_t i = 0; i < lc.elems.size(); ++i) {
    if (!EvalLocatorPredicate(lc, lc.elems[i], i)) continue;
    out.push_back(MakeLogic4VecVal(lc.arena, 32, lc.index_base + i));
    if (method != "find_index") break;
  }
}

static void LocatorMap(const LocatorCtx& lc, std::vector<Logic4Vec>& out) {
  for (size_t i = 0; i < lc.elems.size(); ++i)
    out.push_back(EvalLocatorWithExpr(lc, lc.elems[i], i));
}

static void LocatorUnique(const std::vector<Logic4Vec>& elems, Arena&,
                          std::vector<Logic4Vec>& out) {
  std::vector<uint64_t> seen;
  for (const auto& e : elems) {
    uint64_t v = e.ToUint64();
    bool dup = false;
    for (uint64_t s : seen) {
      if (s == v) {
        dup = true;
        break;
      }
    }
    if (!dup) {
      seen.push_back(v);
      out.push_back(e);
    }
  }
}

// unique_index without a with clause: the index of the first element of each
// distinct value, counted from `index_base` (§7.12.4 with §7.4.2).
static void LocatorUniqueIndex(const std::vector<Logic4Vec>& elems,
                               uint32_t index_base, Arena& arena,
                               std::vector<Logic4Vec>& out) {
  std::vector<uint64_t> seen;
  for (size_t i = 0; i < elems.size(); ++i) {
    uint64_t v = elems[i].ToUint64();
    bool dup = false;
    for (uint64_t s : seen) {
      if (s == v) {
        dup = true;
        break;
      }
    }
    if (!dup) {
      seen.push_back(v);
      out.push_back(MakeLogic4VecVal(arena, 32, index_base + i));
    }
  }
}

// §7.12.1 with §6.11: the element whose value, or whose with expression's
// value, is least for min() and greatest for max(), the first of several equal
// ones, ordered by the signedness of the element type or of the expression.
static void LocatorMinMax(std::string_view method, const LocatorCtx& lc,
                          std::vector<Logic4Vec>& out) {
  if (lc.elems.empty()) return;
  size_t best_idx = 0;
  Logic4Vec best_val =
      lc.with_expr ? EvalLocatorWithExpr(lc, lc.elems[0], 0) : lc.elems[0];
  for (size_t i = 1; i < lc.elems.size(); ++i) {
    Logic4Vec val =
        lc.with_expr ? EvalLocatorWithExpr(lc, lc.elems[i], i) : lc.elems[i];
    if (method == "min" ? OrdersBefore(val, best_val, val.is_signed)
                        : OrdersBefore(best_val, val, val.is_signed)) {
      best_val = val;
      best_idx = i;
    }
  }
  out.push_back(lc.elems[best_idx]);
}

// De-duplicates by the value of the with expression. For each first-seen
// distinct with-value, pushes either the matching element (use_index=false) or
// its index as a 32-bit value (use_index=true).
static void DedupeLocatorResults(const LocatorCtx& lc, bool use_index,
                                 std::vector<Logic4Vec>& out) {
  std::vector<uint64_t> seen;
  for (size_t i = 0; i < lc.elems.size(); ++i) {
    uint64_t v = EvalLocatorWithExpr(lc, lc.elems[i], i).ToUint64();
    bool dup = false;
    for (uint64_t s : seen) {
      if (s == v) {
        dup = true;
        break;
      }
    }
    if (!dup) {
      seen.push_back(v);
      out.push_back(use_index
                        ? MakeLogic4VecVal(lc.arena, 32, lc.index_base + i)
                        : lc.elems[i]);
    }
  }
}

static void LocatorUniqueWith(const LocatorCtx& lc,
                              std::vector<Logic4Vec>& out) {
  DedupeLocatorResults(lc, /*use_index=*/false, out);
}

static void LocatorUniqueIndexWith(const LocatorCtx& lc,
                                   std::vector<Logic4Vec>& out) {
  DedupeLocatorResults(lc, /*use_index=*/true, out);
}

// The receiver's name and the method of the locator `expr`, the call
// `recv.method(...)` or the bare member access `recv.method with (...)`.
// §26.3 admits a package-qualified array as the receiver, `p::a.find(...)`,
// by the "p.a" key ExtractHandleAccessParts answers.
static bool ExtractLocatorParts(const Expr* expr, Arena& arena,
                                MethodCallParts& out) {
  if (expr->kind == ExprKind::kMemberAccess)
    return ExtractHandleAccessParts(expr, arena, out);
  return ExtractHandleMethodCallParts(expr, arena, out);
}

// The receiver of the locator call `expr`, in either of its spellings -- the
// call `recv.method(...)` and the bare member access `recv.method with (...)`
// -- or null for an expression of another shape.
static const Expr* LocatorReceiver(const Expr* expr) {
  const Expr* access = expr->kind == ExprKind::kCall ? expr->lhs : expr;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution || access->rhs == nullptr ||
      access->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  return access->lhs;
}

// §7.12: the associative array a locator or map call is on, whatever names it
// -- a declared array by its bare name, or a property of an object (§8.5): the
// running method's own by its bare name (§8.11) or any object's through a
// handle -- as FindAssocArrayOfBase resolves it. `parts` receives the method
// name, and the receiver's name where the receiver is a bare one. Null where
// the method is no locator, so that no receiver of another method is
// evaluated here, or the receiver names no associative array.
static AssocArrayObject* LocatorAssocReceiver(const Expr* expr,
                                              MethodCallParts& parts,
                                              SimContext& ctx, Arena& arena) {
  const Expr* receiver = LocatorReceiver(expr);
  if (receiver == nullptr) return nullptr;
  parts.method_name =
      (expr->kind == ExprKind::kCall ? expr->lhs : expr)->rhs->text;
  if (!IsLocatorMethod(parts.method_name)) return nullptr;
  if (receiver->kind == ExprKind::kIdentifier) parts.var_name = receiver->text;
  return FindAssocArrayOfBase(receiver, ctx, arena);
}

// Holds the per-entry state shared by the associative-array locator helpers:
// the source keys/values, the iterator-binding context, and the index-type
// width. It also caches the small lambdas (key vector builder, with-expr
// evaluator, match predicate, and sort key) so each dispatch arm reads the same
// way as the indexed-array path.
struct AssocLocatorState {
  const std::vector<Logic4Vec>& keys;
  const std::vector<Logic4Vec>& vals;
  const LocatorCtx& lc;
  bool string_keys;
  SimContext& ctx;
  Arena& arena;

  Logic4Vec KeyVec(size_t i) const { return keys[i]; }
  // Evaluates the with expression for entry i, binding the element iterator to
  // the value and the index iterator to the key, a string for a string index.
  Logic4Vec EvalWith(size_t i) const {
    ctx.PushScope();
    auto* item_var =
        ctx.CreateLocalVariable(lc.iter_name, vals[i].width, vals[i].is_signed);
    item_var->value = vals[i];
    auto* idx_var = ctx.CreateLocalVariable(lc.idx_var_name, keys[i].width);
    idx_var->value = KeyVec(i);
    if (string_keys) ctx.RegisterStringVariable(lc.idx_var_name);
    Logic4Vec r = EvalExpr(lc.with_expr, ctx, arena);
    ctx.PopScope();
    return r;
  }
  bool Matches(size_t i) const { return EvalWith(i).ToUint64() != 0; }
  // The value min() and max() order entry i by: its with expression's where
  // there is one, and its own where there is not.
  Logic4Vec OrderValue(size_t i) const {
    return lc.with_expr ? EvalWith(i) : vals[i];
  }
};

// Forward scan over every entry, pushing the projection of each matching entry.
// Used by the "find all" (no break) and "find first" (break) arms; the latter
// passes stop_after_first=true.
static void AssocScanForward(const AssocLocatorState& st, bool stop_after_first,
                             Logic4Vec (*project)(const AssocLocatorState&,
                                                  size_t),
                             std::vector<Logic4Vec>& out) {
  for (size_t i = 0; i < st.vals.size(); ++i)
    if (st.Matches(i)) {
      out.push_back(project(st, i));
      if (stop_after_first) break;
    }
}

// Reverse scan, pushing the projection of the last matching entry only.
static void AssocScanLast(const AssocLocatorState& st,
                          Logic4Vec (*project)(const AssocLocatorState&,
                                               size_t),
                          std::vector<Logic4Vec>& out) {
  for (size_t i = st.vals.size(); i > 0; --i)
    if (st.Matches(i - 1)) {
      out.push_back(project(st, i - 1));
      break;
    }
}

static Logic4Vec ProjectVal(const AssocLocatorState& st, size_t i) {
  return st.vals[i];
}

static Logic4Vec ProjectKey(const AssocLocatorState& st, size_t i) {
  return st.KeyVec(i);
}

static void AssocLocatorFind(std::string_view method,
                             const AssocLocatorState& st,
                             std::vector<Logic4Vec>& out) {
  if (method == "find") {
    AssocScanForward(st, /*stop_after_first=*/false, ProjectVal, out);
  } else if (method == "find_first") {
    AssocScanForward(st, /*stop_after_first=*/true, ProjectVal, out);
  } else {  // find_last
    AssocScanLast(st, ProjectVal, out);
  }
}

static void AssocLocatorFindIndex(std::string_view method,
                                  const AssocLocatorState& st,
                                  std::vector<Logic4Vec>& out) {
  if (method == "find_index") {
    AssocScanForward(st, /*stop_after_first=*/false, ProjectKey, out);
  } else if (method == "find_first_index") {
    AssocScanForward(st, /*stop_after_first=*/true, ProjectKey, out);
  } else {  // find_last_index
    AssocScanLast(st, ProjectKey, out);
  }
}

static void AssocLocatorMinMax(std::string_view method,
                               const AssocLocatorState& st,
                               std::vector<Logic4Vec>& out) {
  const auto& vals = st.vals;
  if (vals.empty()) return;
  // §7.12.1 with §6.11: ordered as LocatorMinMax orders an indexed array's.
  size_t best = 0;
  Logic4Vec best_key = st.OrderValue(0);
  for (size_t i = 1; i < vals.size(); ++i) {
    Logic4Vec k = st.OrderValue(i);
    if (method == "min" ? OrdersBefore(k, best_key, k.is_signed)
                        : OrdersBefore(best_key, k, k.is_signed)) {
      best_key = k;
      best = i;
    }
  }
  out.push_back(vals[best]);
}

static void AssocLocatorUnique(std::string_view method,
                               const AssocLocatorState& st,
                               std::vector<Logic4Vec>& out) {
  const auto& vals = st.vals;
  std::vector<uint64_t> seen;
  for (size_t i = 0; i < vals.size(); ++i) {
    uint64_t v = st.OrderValue(i).ToUint64();
    bool dup = false;
    for (uint64_t s : seen)
      if (s == v) {
        dup = true;
        break;
      }
    if (dup) continue;
    seen.push_back(v);
    out.push_back(method == "unique" ? vals[i] : st.KeyVec(i));
  }
}

// Dispatches a single associative-array locator method to its dedicated helper.
// Returns false for any method name that is not a 7.12.1 locator (mirroring the
// indexed-array fall-through), true otherwise.
static bool DispatchAssocLocator(std::string_view method,
                                 const AssocLocatorState& st,
                                 std::vector<Logic4Vec>& out) {
  if (method == "find" || method == "find_first" || method == "find_last") {
    AssocLocatorFind(method, st, out);
  } else if (method == "find_index" || method == "find_first_index" ||
             method == "find_last_index") {
    AssocLocatorFindIndex(method, st, out);
  } else if (method == "min" || method == "max") {
    AssocLocatorMinMax(method, st, out);
  } else if (method == "unique" || method == "unique_index") {
    AssocLocatorUnique(method, st, out);
  } else {
    return false;
  }
  return true;
}

// §7.12.1 — array locator methods over an associative array. Two rules differ
// from the indexed-array case: index locators (find_index/.../unique_index)
// return a queue of the *index type* holding the matching keys rather than a
// queue of int holding 0-based positions; and "first"/"last" are the entries
// with the smallest/largest index (the first()/last() ordering of 7.9), which a
// std::map gives for free by visiting keys in ascending order, for integral
// and string keys alike.
// Emits the mandatory-with-clause diagnostic for the associative-array find*
// locators. Returns false (with an error raised) when a with clause is required
// but absent; true otherwise.
static bool CheckAssocWithClauseRequired(std::string_view method,
                                         const Expr* expr, SimContext& ctx) {
  const bool kNeedsWith = method == "find" || method == "find_index" ||
                          method == "find_first" ||
                          method == "find_first_index" ||
                          method == "find_last" || method == "find_last_index";
  if (!expr->with_expr && kNeedsWith) {
    ctx.GetDiag().Error(expr->range.start,
                        "array locator method '" + std::string(method) +
                            "' requires a 'with' clause",
                        Subclause("7.12.1"));
    return false;
  }
  return true;
}

void CollectAssocKeyVals(const AssocArrayObject& aa, Arena& arena,
                         std::vector<Logic4Vec>& keys,
                         std::vector<Logic4Vec>& vals) {
  if (aa.is_string_key) {
    for (const auto& [k, v] : aa.str_data) {
      keys.push_back(StringToLogic4Vec(arena, k));
      vals.push_back(v);
      TakeElementSignedness(aa, vals.back());
    }
    return;
  }
  for (const auto& [k, v] : aa.int_data) {
    Logic4Vec key =
        MakeLogic4VecVal(arena, aa.index_width, static_cast<uint64_t>(k));
    key.is_signed = aa.is_index_signed;
    keys.push_back(key);
    vals.push_back(v);
    TakeElementSignedness(aa, vals.back());
  }
}

// §7.12.1 — the evaluation environment shared by every array locator entry
// point: the method-call expression (which carries the optional with clause),
// the simulator context the iterators are bound in, and the arena that backs
// the freshly built result vectors. Bundled so the locator helpers stay at or
// below the parameter cap while still naming a single domain object.
struct LocatorEnv {
  const Expr* expr;
  SimContext& ctx;
  Arena& arena;
};

// §7.12.1 — the indexed-array subject of a locator query: the collapsed element
// vector and whether those elements are strings, evaluated inside a LocatorEnv.
// The indexed locator family (unique/unique_index/min/max and find*) all act on
// exactly this object, so they share one struct. `var_name` and `info` name
// the array and its shape, which a multidimensional array's subarray
// elements are bound from (§7.4.4).
struct IndexedLocatorInput {
  LocatorEnv env;
  const std::vector<Logic4Vec>& elems;
  bool is_str;
  std::string_view var_name;
  const ArrayInfo& info;
};

// §7.10: the queue or dynamic array `name` names, where `info` describes one
// and its elements are queues or fixed-size arrays; null otherwise.
static const QueueObject* QueueOfQueuesNamed(std::string_view name,
                                             const ArrayInfo& info,
                                             SimContext& ctx) {
  if (!info.is_dynamic) return nullptr;
  const QueueObject* q = ctx.FindQueue(name);
  return q != nullptr && q->elements_are_queues ? q : nullptr;
}

// The iterator context of the indexed locator `in`, its indices counted from
// the array's low bound and its iterator bound to each subarray where the
// array's elements are subarrays, or to each element's queue where they are
// queues or fixed-size arrays kept as queues.
static LocatorCtx MakeIndexedLocatorCtx(const IndexedLocatorInput& in) {
  const LocatorEnv& env = in.env;
  LocatorCtx lc =
      MakeLocatorCtx(in.elems, in.is_str, env.expr, env.ctx, env.arena);
  lc.index_base = in.info.lo;
  lc.is_descending = in.info.is_descending;
  lc.element_queue_owner = QueueOfQueuesNamed(in.var_name, in.info, env.ctx);
  if (HasSubarrayElements(in.info)) {
    lc.subarray_owner = in.var_name;
    lc.subarray_info = &in.info;
  }
  return lc;
}

static bool TryCollectAssocLocatorResult(const LocatorEnv& env,
                                         const MethodCallParts& parts,
                                         AssocArrayObject& aa,
                                         std::vector<Logic4Vec>& out) {
  std::string_view method = parts.method_name;
  if (method == "map") return false;  // not a 7.12.1 locator method

  if (!CheckAssocWithClauseRequired(method, env.expr, env.ctx)) return false;

  std::vector<Logic4Vec> keys;
  std::vector<Logic4Vec> vals;
  CollectAssocKeyVals(aa, env.arena, keys, vals);

  LocatorCtx lc =
      MakeLocatorCtx(vals, /*is_str=*/false, env.expr, env.ctx, env.arena);
  AssocLocatorState st{keys, vals, lc, aa.is_string_key, env.ctx, env.arena};
  return DispatchAssocLocator(method, st, out);
}

// Handles the indexed-array locators whose with clause is optional (unique,
// unique_index, min, max): builds the iterator context only when a with clause
// is present and routes to the matching helper. Sets *handled when the method
// is one of these and returns the result the caller should propagate.
// unique: dedupe by with-value when a with clause is present, otherwise by the
// element value itself.
static void RunIndexedUnique(const IndexedLocatorInput& in,
                             std::vector<Logic4Vec>& out) {
  const LocatorEnv& env = in.env;
  if (env.expr->with_expr) {
    LocatorCtx lc = MakeIndexedLocatorCtx(in);
    LocatorUniqueWith(lc, out);
  } else {
    LocatorUnique(in.elems, env.arena, out);
  }
}

// unique_index: same dedupe rule as unique, but emits indices.
static void RunIndexedUniqueIndex(const IndexedLocatorInput& in,
                                  std::vector<Logic4Vec>& out) {
  const LocatorEnv& env = in.env;
  if (env.expr->with_expr) {
    LocatorCtx lc = MakeIndexedLocatorCtx(in);
    LocatorUniqueIndexWith(lc, out);
  } else {
    LocatorUniqueIndex(in.elems, in.info.lo, env.arena, out);
  }
}

static void RunIndexedMinMax(std::string_view method,
                             const IndexedLocatorInput& in,
                             std::vector<Logic4Vec>& out) {
  LocatorCtx lc = MakeIndexedLocatorCtx(in);
  LocatorMinMax(method, lc, out);
}

static bool TryIndexedOptionalWithLocator(std::string_view method,
                                          const IndexedLocatorInput& in,
                                          std::vector<Logic4Vec>& out,
                                          bool& handled) {
  handled = true;
  if (method == "unique") {
    RunIndexedUnique(in, out);
    return true;
  }
  if (method == "unique_index") {
    RunIndexedUniqueIndex(in, out);
    return true;
  }
  if (method == "min" || method == "max") {
    RunIndexedMinMax(method, in, out);
    return true;
  }
  handled = false;
  return false;
}

// Emits the mandatory-with-clause diagnostics for the indexed-array locators
// that have no value without a predicate (map and the find* family). Returns
// false when an error was raised so the caller can short-circuit; returns true
// when the with clause is present and evaluation may proceed.
static bool CheckIndexedWithClauseRequired(std::string_view method,
                                           const Expr* expr, SimContext& ctx) {
  // §7.12.5 — map() replaces each element with the value of its with clause,
  // and that clause is required: there is nothing to evaluate without it, so a
  // bare map() is illegal rather than a silent no-op.
  if (method == "map" && !expr->with_expr) {
    ctx.GetDiag().Error(expr->range.start,
                        "array method 'map' requires a 'with' clause",
                        Subclause("7.12.5"));
    return false;
  }

  if (!expr->with_expr) {
    // §7.12.1 — the with clause is mandatory for the element- and
    // index-finding locators; it carries the Boolean predicate they filter on.
    // A bare find* call is illegal, so flag it instead of silently yielding
    // nothing.
    if (method == "find" || method == "find_index" || method == "find_first" ||
        method == "find_first_index" || method == "find_last" ||
        method == "find_last_index") {
      ctx.GetDiag().Error(expr->range.start,
                          "array locator method '" + std::string(method) +
                              "' requires a 'with' clause",
                          Subclause("7.12.1"));
    }
    return false;
  }
  return true;
}

// §7.12.1 — locator methods operate on any unpacked array, which includes a
// queue (§7.10). A queue carries no ArrayInfo of its own, so it is described as
// a dynamic array; the element-collection path then reads its elements from the
// queue store keyed by the same name.
static bool DescribeQueueAsArray(std::string_view name, SimContext& ctx,
                                 ArrayInfo& queue_info) {
  auto* q = ctx.FindQueue(name);
  if (!q) return false;
  queue_info.is_dynamic = true;
  queue_info.elem_width = q->elem_width;
  return true;
}

// §7.12.1/§7.12.5 — run the named locator (or map) over the collapsed elements.
static void DispatchIndexedLocator(std::string_view method,
                                   const LocatorCtx& lc,
                                   std::vector<Logic4Vec>& out) {
  if (method == "map") {
    LocatorMap(lc, out);
    return;
  }
  if (method == "find_index" || method == "find_first_index" ||
      method == "find_last_index") {
    LocatorFindIndex(method, lc, out);
    return;
  }
  LocatorFindDispatch(method, lc, out);
}

// The offsets 0 to `count` - 1, one for each element of an array whose
// elements are arrays.
static std::vector<Logic4Vec> SubarrayOffsets(size_t count, Arena& arena) {
  std::vector<Logic4Vec> offsets;
  offsets.reserve(count);
  for (size_t i = 0; i < count; ++i)
    offsets.push_back(MakeLogic4VecVal(arena, 32, i));
  return offsets;
}

// The element list a locator over the array `name` walks: each element's
// value, or, where the elements are arrays that no one value holds -- the
// subarrays of a multidimensional array (§7.4.4) and the queues or
// fixed-size arrays of a queue or dynamic array (§7.10) -- each element's
// offset, which a locator that returns elements returns for
// TryCollectLocatorRows to read the elements by.
static std::vector<Logic4Vec> LocatorElements(std::string_view name,
                                              const ArrayInfo& info,
                                              SimContext& ctx, Arena& arena) {
  if (HasSubarrayElements(info))
    return SubarrayOffsets(info.dim_sizes[0], arena);
  if (const QueueObject* q = QueueOfQueuesNamed(name, info, ctx))
    return SubarrayOffsets(q->elements.size(), arena);
  return CollectVecElements(name, info, ctx, arena);
}

static bool CollectLocatorResult(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::vector<Logic4Vec>& out) {
  MethodCallParts parts;
  // A property reached through a handle has no bare name to extract, so the
  // associative receiver is asked for first, by expression.
  AssocArrayObject* aa = LocatorAssocReceiver(expr, parts, ctx, arena);
  if (aa == nullptr && !ExtractLocatorParts(expr, arena, parts)) return false;
  if (!IsLocatorMethod(parts.method_name)) return false;

  if (!expr->args.empty() && !expr->with_expr) {
    ctx.GetDiag().Error(expr->args.front()->range.start,
                        "iterator argument without 'with' clause",
                        Subclause("7.12"));
    return false;
  }

  // §7.12 with §7.2: the iterator of every locator's with clause, optional or
  // required, over an associative or an indexed array, reads the members of
  // the structure element it holds.
  IteratorLayout layout(ExtractIterNames(expr).iter_name, parts.var_name, ctx);

  // Associative arrays are stored separately and honor index-type returns
  // and key ordering through a dedicated path.
  if (aa != nullptr)
    return TryCollectAssocLocatorResult(LocatorEnv{expr, ctx, arena}, parts,
                                        *aa, out);
  auto* info = ctx.FindArrayInfo(parts.var_name);
  ArrayInfo queue_info;
  if (!info) {
    if (!DescribeQueueAsArray(parts.var_name, ctx, queue_info)) return false;
    info = &queue_info;
  }

  auto elems = LocatorElements(parts.var_name, *info, ctx, arena);
  bool is_str = IsStringArray(parts.var_name, *info, ctx);

  IndexedLocatorInput in{LocatorEnv{expr, ctx, arena}, elems, is_str,
                         parts.var_name, *info};
  bool handled = false;
  bool optional_result =
      TryIndexedOptionalWithLocator(parts.method_name, in, out, handled);
  if (handled) return optional_result;

  if (!CheckIndexedWithClauseRequired(parts.method_name, expr, ctx))
    return false;

  LocatorCtx lc = MakeIndexedLocatorCtx(in);
  DispatchIndexedLocator(parts.method_name, lc, out);
  return true;
}

// §7.12.1: the locators that return elements of the array rather than their
// indices or the values of a with clause.
static bool ReturnsElements(std::string_view method) {
  return method == "find" || method == "find_first" || method == "find_last" ||
         method == "min" || method == "max" || method == "unique";
}

// Every locator that returns elements needs a with clause to select rows, as
// the find family requires one and the relational operators min, max and
// unique would otherwise order by are not defined for an unpacked array; a
// call without one is left to the path that reports it.
bool TryCollectLocatorRows(const Expr* expr, SimContext& ctx, Arena& arena,
                           LocatorRows& out) {
  MethodCallParts parts;
  if (expr->with_expr == nullptr || !ExtractLocatorParts(expr, arena, parts) ||
      !ReturnsElements(parts.method_name))
    return false;
  const ArrayInfo* info = ctx.FindArrayInfo(parts.var_name);
  const QueueObject* queue = ctx.FindQueue(parts.var_name);
  bool rows_of_array = info != nullptr && info->dim_sizes.size() == 2;
  bool elements_of_queue = queue != nullptr && queue->elements_are_queues;
  if (!rows_of_array && !elements_of_queue) return false;
  std::vector<Logic4Vec> picked;
  if (!CollectLocatorResult(expr, ctx, arena, picked)) return false;
  out.array_name = parts.var_name;
  out.info = info;
  out.queue = elements_of_queue ? queue : nullptr;
  for (const Logic4Vec& offset : picked)
    out.offsets.push_back(static_cast<uint32_t>(offset.ToUint64()));
  return true;
}

// §7.12.1 with §8.5: a locator on a queue property, `h.q.find with (...)` or
// a bare `q` in a method, is run on the queue QueuePropertyReceiver names.
bool TryCollectLocatorResult(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::vector<Logic4Vec>& out) {
  if (CollectLocatorResult(expr, ctx, arena, out)) return true;
  const Expr* access = expr->kind == ExprKind::kCall ? expr->lhs : expr;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->rhs == nullptr || !IsLocatorMethod(access->rhs->text)) {
    return false;
  }
  QueuePropertyReceiver receiver(expr, ctx, arena);
  return receiver.Call() != nullptr &&
         CollectLocatorResult(receiver.Call(), ctx, arena, out);
}

// Maps a string-keyed associative source: preserves the string key set and
// replaces each stored value with the with expression, binding the element
// iterator to the value and the index iterator to the key string (so a with
// expression may reference either). Split out so the integer- and string-keyed
// index types each read straightforwardly.
static void MapStringKeyedAssoc(const LocatorEnv& env, const LocatorCtx& lc,
                                const AssocArrayObject& aa,
                                AssocArrayObject& out) {
  SimContext& ctx = env.ctx;
  for (const auto& [key, val] : aa.str_data) {
    ctx.PushScope();
    auto* item_var =
        ctx.CreateLocalVariable(lc.iter_name, val.width, aa.is_signed);
    item_var->value = val;
    Logic4Vec key_vec = StringToLogic4Vec(env.arena, key);
    auto* idx_var = ctx.CreateLocalVariable(lc.idx_var_name, key_vec.width);
    idx_var->value = key_vec;
    ctx.RegisterStringVariable(lc.idx_var_name);
    Logic4Vec mapped = EvalExpr(lc.with_expr, ctx, env.arena);
    ctx.PopScope();
    out.str_data[key] = mapped;
    out.elem_width = mapped.width;
  }
}

// Maps an integer-keyed associative source, binding the element iterator to the
// stored value and the index iterator to the key at the source's index width.
static void MapIntKeyedAssoc(const LocatorEnv& env, const LocatorCtx& lc,
                             const AssocArrayObject& aa,
                             AssocArrayObject& out) {
  SimContext& ctx = env.ctx;
  const uint32_t kIw = aa.index_width;
  for (const auto& [key, val] : aa.int_data) {
    ctx.PushScope();
    auto* item_var =
        ctx.CreateLocalVariable(lc.iter_name, val.width, aa.is_signed);
    item_var->value = val;
    auto* idx_var = ctx.CreateLocalVariable(lc.idx_var_name, kIw);
    idx_var->value =
        MakeLogic4VecVal(env.arena, kIw, static_cast<uint64_t>(key));
    Logic4Vec mapped = EvalExpr(lc.with_expr, ctx, env.arena);
    ctx.PopScope();
    out.int_data[key] = mapped;
    out.elem_width = mapped.width;
  }
}

// §7.12.5 — map() over an associative array. Unlike the locator methods, map
// does not collapse the array to a queue: it produces an associative array
// whose set of index values and index type match the source, with each stored
// value replaced by the value of the with expression. The with clause is
// required, and each result element takes the self-determined type of that
// expression (carried by the width of the evaluated value). Both integer- and
// string-keyed index types are handled; the returned array carries the source's
// key set and index type unchanged.
bool TryCollectAssocMapResult(const Expr* expr, SimContext& ctx, Arena& arena,
                              AssocArrayObject& out) {
  MethodCallParts parts;
  auto* aa = LocatorAssocReceiver(expr, parts, ctx, arena);
  if (!aa) return false;
  if (parts.method_name != "map") return false;
  if (!expr->with_expr) {
    ctx.GetDiag().Error(expr->range.start,
                        "array method 'map' requires a 'with' clause",
                        Subclause("7.12.5"));
    return false;
  }

  // The returned array's range and index type match the source: carry over the
  // index metadata and reuse the source keys unchanged.
  out.index_width = aa->index_width;
  out.is_index_signed = aa->is_index_signed;
  out.is_wildcard = aa->is_wildcard;
  out.is_string_key = aa->is_string_key;
  out.int_data.clear();
  out.str_data.clear();

  std::vector<Logic4Vec> vals;
  if (aa->is_string_key) {
    vals.reserve(aa->str_data.size());
    for (const auto& [k, v] : aa->str_data) vals.push_back(v);
    LocatorCtx lc = MakeLocatorCtx(vals, /*is_str=*/false, expr, ctx, arena);
    MapStringKeyedAssoc(LocatorEnv{expr, ctx, arena}, lc, *aa, out);
    return true;
  }

  vals.reserve(aa->int_data.size());
  for (const auto& [k, v] : aa->int_data) vals.push_back(v);
  LocatorCtx lc = MakeLocatorCtx(vals, /*is_str=*/false, expr, ctx, arena);
  MapIntKeyedAssoc(LocatorEnv{expr, ctx, arena}, lc, *aa, out);
  return true;
}

}  // namespace delta
