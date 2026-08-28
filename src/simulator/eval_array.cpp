#include "simulator/eval_array.h"

#include <algorithm>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/eval_array_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

static void WriteVecElements(std::string_view var_name, const ArrayInfo& info,
                             const std::vector<Logic4Vec>& vals,
                             SimContext& ctx);

// The 'with'-clause iteration binding for array reduction/ordering methods
// (§7.12). Each element is evaluated with the iterator variable (named by
// iter_name) and its index variable (idx_var_name) bound in a fresh scope.
// ctx/arena are the evaluation environment those bindings live in.
struct WithIterEnv {
  std::string_view iter_name;
  const std::string& idx_var_name;
  SimContext& ctx;
  Arena& arena;
};

static std::vector<uint64_t> CollectElements(std::string_view var_name,
                                             const ArrayInfo& info,
                                             SimContext& ctx) {
  if (info.is_dynamic) {
    auto* q = ctx.FindQueue(var_name);
    if (!q) return {};
    std::vector<uint64_t> vals;
    vals.reserve(q->elements.size());
    for (const auto& e : q->elements) vals.push_back(e.ToUint64());
    return vals;
  }
  std::vector<uint64_t> vals;
  vals.reserve(info.size);
  for (uint32_t i = 0; i < info.size; ++i) {
    uint32_t idx = info.lo + i;
    auto name = std::string(var_name) + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(name);
    vals.push_back(v ? v->value.ToUint64() : 0);
  }
  return vals;
}

static void WriteElements(std::string_view var_name, const ArrayInfo& info,
                          const std::vector<uint64_t>& vals, SimContext& ctx,
                          Arena& arena) {
  if (info.is_dynamic) {
    auto* q = ctx.FindQueue(var_name);
    if (!q) return;
    q->elements.resize(vals.size());
    for (size_t i = 0; i < vals.size(); ++i)
      q->elements[i] = MakeLogic4VecVal(arena, q->elem_width, vals[i]);
    ++q->generation;
    return;
  }
  for (uint32_t i = 0; i < info.size && i < vals.size(); ++i) {
    uint32_t idx = info.lo + i;
    auto name = std::string(var_name) + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(name);
    if (v) v->value = MakeLogic4VecVal(arena, info.elem_width, vals[i]);
  }
}

// The identity permutation over `count` positions. Each ordering method of
// §7.12.2 sorts, reverses or shuffles this vector instead of the values, so
// that where every element moved is still known once the new value list has
// been built from it.
static std::vector<size_t> IdentityOrder(size_t count) {
  std::vector<size_t> order(count);
  for (size_t i = 0; i < count; ++i) order[i] = i;
  return order;
}

// Applies a permutation to a value list: `order[i]` is the position the value
// now at i came from, the same meaning the permutation carries into
// ApplyDynArrayIdPermutation.
template <typename T>
static std::vector<T> GatherByOrder(const std::vector<T>& vals,
                                    const std::vector<size_t>& order) {
  std::vector<T> out(order.size());
  for (size_t i = 0; i < order.size(); ++i) out[i] = vals[order[i]];
  return out;
}

// §7.10.3: an argument passed by reference names the element it was taken on,
// so it must keep naming that element after the array is reordered. A dynamic
// array is backed by a QueueObject whose element_ids run parallel to its
// elements, and a ref argument is recorded against the id at the index it was
// taken at; moving an element without moving its id sends the write-back to
// whichever element landed at that index. So every §7.12.2 ordering method
// applies its permutation here as well as to the values. `order[i]` is the
// index the element now at position i came from. element_ids can be shorter
// than elements, so an entry whose source or destination index is past its end
// is skipped rather than read or written out of range. Nothing is done for a
// fixed-size array, whose elements are ordinary variables and carry no ids.
static void ApplyDynArrayIdPermutation(std::string_view var_name,
                                       const ArrayInfo& info,
                                       const std::vector<size_t>& order,
                                       SimContext& ctx) {
  if (!info.is_dynamic) return;
  auto* q = ctx.FindQueue(var_name);
  if (!q) return;
  auto& ids = q->element_ids;
  std::vector<uint64_t> reordered(ids.size());
  for (size_t i = 0; i < order.size(); ++i) {
    if (i < reordered.size() && order[i] < ids.size())
      reordered[i] = ids[order[i]];
  }
  ids = std::move(reordered);
}

std::vector<Logic4Vec> CollectVecElements(std::string_view var_name,
                                          const ArrayInfo& info,
                                          SimContext& ctx, Arena& arena) {
  if (info.is_dynamic) {
    auto* q = ctx.FindQueue(var_name);
    if (!q) return {};
    return q->elements;
  }
  std::vector<Logic4Vec> vals;
  vals.reserve(info.size);
  for (uint32_t i = 0; i < info.size; ++i) {
    uint32_t idx = info.lo + i;
    auto name = std::string(var_name) + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(name);
    vals.push_back(v ? v->value : MakeLogic4VecVal(arena, info.elem_width, 0));
  }
  return vals;
}

static Logic4Vec ArraySum(std::string_view var_name, const ArrayInfo& info,
                          SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  uint64_t result = 0;
  for (auto v : vals) result += v;
  return MakeLogic4VecVal(arena, info.elem_width, result);
}

static Logic4Vec ArrayProduct(std::string_view var_name, const ArrayInfo& info,
                              SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  uint64_t result = 1;
  for (auto v : vals) result *= v;
  return MakeLogic4VecVal(arena, info.elem_width, result);
}

static Logic4Vec ArrayAnd(std::string_view var_name, const ArrayInfo& info,
                          SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  uint64_t result = vals.empty() ? 0 : vals[0];
  for (size_t i = 1; i < vals.size(); ++i) result &= vals[i];
  return MakeLogic4VecVal(arena, info.elem_width, result);
}

static Logic4Vec ArrayOr(std::string_view var_name, const ArrayInfo& info,
                         SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  uint64_t result = 0;
  for (auto v : vals) result |= v;
  return MakeLogic4VecVal(arena, info.elem_width, result);
}

static Logic4Vec ArrayXor(std::string_view var_name, const ArrayInfo& info,
                          SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  uint64_t result = 0;
  for (auto v : vals) result ^= v;
  return MakeLogic4VecVal(arena, info.elem_width, result);
}

IterNames ExtractIterNames(const Expr* expr) {
  std::string_view iter_name = "item";
  std::string_view index_name = "index";
  if (!expr->args.empty() && expr->args[0] &&
      expr->args[0]->kind == ExprKind::kIdentifier) {
    iter_name = expr->args[0]->text;
  }
  if (expr->args.size() >= 2 && expr->args[1] &&
      expr->args[1]->kind == ExprKind::kIdentifier) {
    index_name = expr->args[1]->text;
  }
  std::string idx_var_name =
      std::string(iter_name) + "." + std::string(index_name);
  return IterNames{iter_name, index_name, std::move(idx_var_name)};
}

static Logic4Vec EvalWithExprForElement(const Expr* with_expr,
                                        const WithIterEnv& env,
                                        const Logic4Vec& elem, size_t index) {
  env.ctx.PushScope();
  auto* item_var = env.ctx.CreateLocalVariable(env.iter_name, elem.width);
  item_var->value = elem;
  auto* idx_var = env.ctx.CreateLocalVariable(env.idx_var_name, 32);
  idx_var->value =
      MakeLogic4VecVal(env.arena, 32, static_cast<uint64_t>(index));
  Logic4Vec ev = EvalExpr(with_expr, env.ctx, env.arena);
  env.ctx.PopScope();
  return ev;
}

static std::vector<uint64_t> EvalReduceWithValues(
    const std::vector<Logic4Vec>& elems, const Expr* expr,
    const WithIterEnv& env, uint32_t& result_width) {
  std::vector<uint64_t> vals;
  vals.reserve(elems.size());
  result_width = 0;
  for (size_t i = 0; i < elems.size(); ++i) {
    Logic4Vec ev = EvalWithExprForElement(expr->with_expr, env, elems[i], i);
    vals.push_back(ev.ToUint64());
    if (i == 0) result_width = ev.width;
  }
  return vals;
}

static uint64_t ReduceSumVals(const std::vector<uint64_t>& vals) {
  uint64_t result = 0;
  for (auto v : vals) result += v;
  return result;
}

static uint64_t ReduceProductVals(const std::vector<uint64_t>& vals) {
  uint64_t result = 1;
  for (auto v : vals) result *= v;
  return result;
}

static uint64_t ReduceAndVals(const std::vector<uint64_t>& vals) {
  uint64_t result = vals.empty() ? 0 : vals[0];
  for (size_t i = 1; i < vals.size(); ++i) result &= vals[i];
  return result;
}

static uint64_t ReduceOrVals(const std::vector<uint64_t>& vals) {
  uint64_t result = 0;
  for (auto v : vals) result |= v;
  return result;
}

static uint64_t ReduceXorVals(const std::vector<uint64_t>& vals) {
  uint64_t result = 0;
  for (auto v : vals) result ^= v;
  return result;
}

static uint64_t ApplyReduction(std::string_view method,
                               const std::vector<uint64_t>& vals) {
  if (method == "sum") return ReduceSumVals(vals);
  if (method == "product") return ReduceProductVals(vals);
  if (method == "and") return ReduceAndVals(vals);
  if (method == "or") return ReduceOrVals(vals);
  if (method == "xor") return ReduceXorVals(vals);
  return 0;
}

struct ArrayCtx {
  std::string_view var_name;
  const ArrayInfo& info;
  SimContext& ctx;
  Arena& arena;
};

// Reduces the values produced by the with-clause expression of `expr` for each
// element of the named array (§7.12.3). `method` selects the fold and is passed
// explicitly so this serves both the parenthesized call form (method name on
// expr->lhs->rhs) and the bare member-access form `arr.sum with (e)` (method
// name on expr->rhs). The result takes the width of the with expression.
static Logic4Vec ReduceWithExpr(const ArrayCtx& ac, const Expr* expr,
                                std::string_view method) {
  auto elems = CollectVecElements(ac.var_name, ac.info, ac.ctx, ac.arena);
  auto names = ExtractIterNames(expr);
  WithIterEnv env{names.iter_name, names.idx_var_name, ac.ctx, ac.arena};

  uint32_t result_width = 0;
  auto vals = EvalReduceWithValues(elems, expr, env, result_width);
  if (result_width == 0) result_width = ac.info.elem_width;

  uint64_t result = ApplyReduction(method, vals);
  return MakeLogic4VecVal(ac.arena, result_width, result);
}

static Logic4Vec ArraySize(std::string_view var_name, const ArrayInfo& info,
                           SimContext& ctx, Arena& arena) {
  if (info.is_dynamic) {
    auto* q = ctx.FindQueue(var_name);
    return MakeLogic4VecVal(arena, 32, q ? q->elements.size() : 0);
  }
  return MakeLogic4VecVal(arena, 32, info.size);
}

static Logic4Vec ArrayMin(std::string_view var_name, const ArrayInfo& info,
                          SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  if (vals.empty()) return MakeLogic4VecVal(arena, info.elem_width, 0);
  uint64_t result = *std::min_element(vals.begin(), vals.end());
  return MakeLogic4VecVal(arena, info.elem_width, result);
}

static Logic4Vec ArrayMax(std::string_view var_name, const ArrayInfo& info,
                          SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  if (vals.empty()) return MakeLogic4VecVal(arena, info.elem_width, 0);
  uint64_t result = *std::max_element(vals.begin(), vals.end());
  return MakeLogic4VecVal(arena, info.elem_width, result);
}

static bool IsReductionMethod(std::string_view method) {
  return method == "sum" || method == "product" || method == "and" ||
         method == "or" || method == "xor";
}

// Resolves the ArrayInfo a reduction should read. Registered fixed and dynamic
// arrays return their own info. A queue ([$]) is not registered as ArrayInfo,
// but §7.12.3 reduction methods apply to any unpacked integral array; when a
// reduction is requested on a queue, present a dynamic-array view backed by the
// queue's elements so the shared reduction path reads them. `scratch` provides
// storage for that synthesized view. Non-reduction methods on a queue return
// nullptr so they fall through to the dedicated queue dispatch.
static const ArrayInfo* ArrayInfoForReduction(std::string_view var_name,
                                              std::string_view method,
                                              SimContext& ctx,
                                              ArrayInfo& scratch) {
  if (auto* info = ctx.FindArrayInfo(var_name)) return info;
  if (!IsReductionMethod(method)) return nullptr;
  if (auto* q = ctx.FindQueue(var_name)) {
    scratch.is_dynamic = true;
    scratch.elem_width = q->elem_width;
    scratch.size = static_cast<uint32_t>(q->elements.size());
    return &scratch;
  }
  return nullptr;
}

// §7.12.3: an associative array is an unpacked array of integral values, so the
// reduction methods apply to its stored elements. Collect them in key order
// (int- or string-keyed); the supported operators are commutative, so the
// unspecified iteration order does not affect the result.
static std::vector<Logic4Vec> CollectAssocElements(const AssocArrayObject* aa) {
  std::vector<Logic4Vec> vals;
  if (aa->is_string_key) {
    for (const auto& [key, val] : aa->str_data) vals.push_back(val);
  } else {
    for (const auto& [key, val] : aa->int_data) vals.push_back(val);
  }
  return vals;
}

// Folds an associative array's elements with the named reduction, optionally
// transforming each through the with clause carried by `expr` (null for the
// bare property form). Returns nullopt for non-reduction methods so the caller
// keeps handling its own methods (size, exists, traversal, …).
std::optional<Logic4Vec> TryAssocReduction(AssocArrayObject* aa,
                                           std::string_view method,
                                           const Expr* expr, SimContext& ctx,
                                           Arena& arena) {
  if (!IsReductionMethod(method)) return std::nullopt;
  auto elems = CollectAssocElements(aa);
  if (expr != nullptr && expr->with_expr != nullptr) {
    auto names = ExtractIterNames(expr);
    WithIterEnv env{names.iter_name, names.idx_var_name, ctx, arena};
    uint32_t result_width = 0;
    auto vals = EvalReduceWithValues(elems, expr, env, result_width);
    if (result_width == 0) result_width = aa->elem_width;
    return MakeLogic4VecVal(arena, result_width, ApplyReduction(method, vals));
  }
  std::vector<uint64_t> vals;
  vals.reserve(elems.size());
  for (const auto& e : elems) vals.push_back(e.ToUint64());
  return MakeLogic4VecVal(arena, aa->elem_width, ApplyReduction(method, vals));
}

static bool DispatchReduction(std::string_view method, const ArrayCtx& ac,
                              Logic4Vec& out) {
  if (method == "sum") {
    out = ArraySum(ac.var_name, ac.info, ac.ctx, ac.arena);
    return true;
  }
  if (method == "product") {
    out = ArrayProduct(ac.var_name, ac.info, ac.ctx, ac.arena);
    return true;
  }
  if (method == "and") {
    out = ArrayAnd(ac.var_name, ac.info, ac.ctx, ac.arena);
    return true;
  }
  if (method == "or") {
    out = ArrayOr(ac.var_name, ac.info, ac.ctx, ac.arena);
    return true;
  }
  if (method == "xor") {
    out = ArrayXor(ac.var_name, ac.info, ac.ctx, ac.arena);
    return true;
  }
  return false;
}

static bool DispatchReductionExpr(std::string_view method, const ArrayCtx& ac,
                                  const Expr* expr, Logic4Vec& out) {
  if (!IsReductionMethod(method)) return false;
  if (expr->with_expr) {
    out = ReduceWithExpr(ac, expr, method);
  } else if (method == "sum") {
    out = ArraySum(ac.var_name, ac.info, ac.ctx, ac.arena);
  } else if (method == "product") {
    out = ArrayProduct(ac.var_name, ac.info, ac.ctx, ac.arena);
  } else if (method == "and") {
    out = ArrayAnd(ac.var_name, ac.info, ac.ctx, ac.arena);
  } else if (method == "or") {
    out = ArrayOr(ac.var_name, ac.info, ac.ctx, ac.arena);
  } else if (method == "xor") {
    out = ArrayXor(ac.var_name, ac.info, ac.ctx, ac.arena);
  }
  return true;
}

static bool DispatchQuery(std::string_view method, const ArrayCtx& ac,
                          Logic4Vec& out) {
  if (method == "size") {
    out = ArraySize(ac.var_name, ac.info, ac.ctx, ac.arena);
    return true;
  }
  if (method == "min") {
    out = ArrayMin(ac.var_name, ac.info, ac.ctx, ac.arena);
    return true;
  }
  if (method == "max") {
    out = ArrayMax(ac.var_name, ac.info, ac.ctx, ac.arena);
    return true;
  }
  return false;
}

bool TryEvalArrayMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  ArrayInfo scratch;
  const auto* info =
      ArrayInfoForReduction(parts.var_name, parts.method_name, ctx, scratch);
  if (!info) return false;
  ArrayCtx ac{parts.var_name, *info, ctx, arena};
  if (DispatchReductionExpr(parts.method_name, ac, expr, out)) return true;
  if (DispatchQuery(parts.method_name, ac, out)) return true;

  if (TryExecArrayMethodStmt(expr, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  return false;
}

// §7.12.3: a reduction method written without parentheses carries its with
// clause on the member-access node itself (arr.sum with (e), the form used
// throughout the LRM). EvalMemberAccess routes such a node here so the with
// clause is applied instead of silently dropped. Only reduction methods on an
// unpacked integral array (or queue) are handled; everything else, including
// the no-clause property read, falls through to the ordinary member path.
bool TryEvalArrayReductionWithClause(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  if (expr->kind != ExprKind::kMemberAccess || !expr->with_expr) return false;
  if (!expr->lhs || expr->lhs->kind != ExprKind::kIdentifier) return false;
  if (!expr->rhs || expr->rhs->kind != ExprKind::kIdentifier) return false;
  std::string_view method = expr->rhs->text;
  if (!IsReductionMethod(method)) return false;
  std::string_view var_name = expr->lhs->text;
  ArrayInfo scratch;
  if (const auto* info =
          ArrayInfoForReduction(var_name, method, ctx, scratch)) {
    ArrayCtx ac{var_name, *info, ctx, arena};
    out = ReduceWithExpr(ac, expr, method);
    return true;
  }
  if (auto* aa = ctx.FindAssocArray(var_name)) {
    if (auto reduced = TryAssocReduction(aa, method, expr, ctx, arena)) {
      out = *reduced;
      return true;
    }
  }
  return false;
}

static uint64_t EvalSortKey(const Expr* with_expr, const WithIterEnv& env,
                            const Logic4Vec& elem, size_t index) {
  return EvalWithExprForElement(with_expr, env, elem, index).ToUint64();
}

static std::vector<std::pair<uint64_t, size_t>> BuildSortKeys(
    const std::vector<Logic4Vec>& vals, const Expr* expr,
    const WithIterEnv& env) {
  std::vector<std::pair<uint64_t, size_t>> keys(vals.size());
  for (size_t i = 0; i < vals.size(); ++i) {
    keys[i] = {EvalSortKey(expr->with_expr, env, vals[i], i), i};
  }
  return keys;
}

static void SortKeysByValue(std::vector<std::pair<uint64_t, size_t>>& keys,
                            bool ascending) {
  if (ascending) {
    std::sort(keys.begin(), keys.end());
  } else {
    std::sort(keys.begin(), keys.end(),
              [](const auto& a, const auto& b) { return a.first > b.first; });
  }
}

static std::vector<Logic4Vec> ReorderByKeys(
    const std::vector<Logic4Vec>& vals,
    const std::vector<std::pair<uint64_t, size_t>>& keys) {
  std::vector<Logic4Vec> sorted(vals.size());
  for (size_t i = 0; i < keys.size(); ++i) sorted[i] = vals[keys[i].second];
  return sorted;
}

static void ArraySortWithExpr(const ArrayCtx& ac, const Expr* expr,
                              bool ascending) {
  auto vals = CollectVecElements(ac.var_name, ac.info, ac.ctx, ac.arena);
  auto names = ExtractIterNames(expr);
  WithIterEnv env{names.iter_name, names.idx_var_name, ac.ctx, ac.arena};
  auto keys = BuildSortKeys(vals, expr, env);
  SortKeysByValue(keys, ascending);
  std::vector<Logic4Vec> sorted = ReorderByKeys(vals, keys);
  WriteVecElements(ac.var_name, ac.info, sorted, ac.ctx);
  // The second of each key pair is the index the element now at that position
  // came from, which is the permutation §7.10.3 requires the element ids of a
  // dynamic array to follow.
  std::vector<size_t> order(keys.size());
  for (size_t i = 0; i < keys.size(); ++i) order[i] = keys[i].second;
  ApplyDynArrayIdPermutation(ac.var_name, ac.info, order, ac.ctx);
}

// §7.12.2: reorder a queue by the with-clause key. A queue is not registered as
// an ArrayInfo, so it cannot share the array path above; reorder its elements
// (and their tracking ids, kept parallel) directly by the computed key. The
// permuted ids are always stored, because §7.10.3 makes a reference follow the
// element it was taken on and a lost permutation sends its write-back to the
// element that took that position. Each id is bounds-guarded on its own, so an
// element_ids list that has drifted shorter than elements costs the entries it
// no longer covers rather than the whole permutation.
static void SortQueueByWithExpr(QueueObject* q, const Expr* expr,
                                bool ascending, SimContext& ctx, Arena& arena) {
  auto names = ExtractIterNames(expr);
  WithIterEnv env{names.iter_name, names.idx_var_name, ctx, arena};
  std::vector<std::pair<uint64_t, size_t>> keys(q->elements.size());
  for (size_t i = 0; i < q->elements.size(); ++i)
    keys[i] = {EvalSortKey(expr->with_expr, env, q->elements[i], i), i};
  SortKeysByValue(keys, ascending);
  std::vector<Logic4Vec> new_elems(q->elements.size());
  std::vector<uint64_t> new_ids(q->element_ids.size());
  for (size_t i = 0; i < keys.size(); ++i) {
    new_elems[i] = q->elements[keys[i].second];
    if (i < new_ids.size() && keys[i].second < q->element_ids.size())
      new_ids[i] = q->element_ids[keys[i].second];
  }
  q->elements = std::move(new_elems);
  q->element_ids = std::move(new_ids);
  ++q->generation;
}

// §7.12.2: sort()/rsort() optionally order by the with-clause expression. The
// call form (arr.sort(x) with (e)) is handled by TryExecArrayMethodStmt, but
// the parenthesis-free member form and any queue receiver arrive here as a bare
// member-access node carrying the with clause. Without this, that clause would
// be dropped and the elements sorted by their raw value instead of the key.
bool TryExecArrayOrderingWithClauseStmt(const Expr* expr, SimContext& ctx,
                                        Arena& arena) {
  if (expr == nullptr || expr->kind != ExprKind::kMemberAccess ||
      expr->with_expr == nullptr)
    return false;
  if (expr->lhs == nullptr || expr->lhs->kind != ExprKind::kIdentifier)
    return false;
  if (expr->rhs == nullptr || expr->rhs->kind != ExprKind::kIdentifier)
    return false;
  std::string_view method = expr->rhs->text;
  if (method != "sort" && method != "rsort") return false;
  bool ascending = method == "sort";
  std::string_view var_name = expr->lhs->text;
  if (const ArrayInfo* info = ctx.FindArrayInfo(var_name)) {
    ArrayCtx ac{var_name, *info, ctx, arena};
    ArraySortWithExpr(ac, expr, ascending);
    return true;
  }
  if (QueueObject* q = ctx.FindQueue(var_name)) {
    SortQueueByWithExpr(q, expr, ascending, ctx, arena);
    return true;
  }
  return false;
}

// §7.12.2 sort()/rsort() order the elements by their own value. The order the
// values take is computed over indices rather than over the values themselves,
// so that ApplyDynArrayIdPermutation can move the element ids of a dynamic
// array the same way and keep the §7.10.3 references pointing at their own
// elements.
static void ArraySortByValue(std::string_view var_name, const ArrayInfo& info,
                             bool ascending, SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  auto order = IdentityOrder(vals.size());
  std::sort(order.begin(), order.end(), [&](size_t a, size_t b) {
    return ascending ? vals[a] < vals[b] : vals[a] > vals[b];
  });
  WriteElements(var_name, info, GatherByOrder(vals, order), ctx, arena);
  ApplyDynArrayIdPermutation(var_name, info, order, ctx);
}

static void ArraySort(std::string_view var_name, const ArrayInfo& info,
                      SimContext& ctx, Arena& arena) {
  ArraySortByValue(var_name, info, true, ctx, arena);
}

static void ArrayRsort(std::string_view var_name, const ArrayInfo& info,
                       SimContext& ctx, Arena& arena) {
  ArraySortByValue(var_name, info, false, ctx, arena);
}

static void WriteVecElements(std::string_view var_name, const ArrayInfo& info,
                             const std::vector<Logic4Vec>& vals,
                             SimContext& ctx) {
  if (info.is_dynamic) {
    auto* q = ctx.FindQueue(var_name);
    if (!q) return;
    q->elements.resize(vals.size());
    for (size_t i = 0; i < vals.size(); ++i) q->elements[i] = vals[i];
    ++q->generation;
    return;
  }
  for (uint32_t i = 0; i < info.size && i < vals.size(); ++i) {
    uint32_t idx = info.lo + i;
    auto name = std::string(var_name) + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(name);
    if (v) v->value = vals[i];
  }
}

// §7.12.2 reverse() reverses the element order. Reversing the index vector and
// gathering through it leaves the permutation available for the element ids of
// a dynamic array, which §7.10.3 requires to move with their elements.
static void ArrayReverse(std::string_view var_name, const ArrayInfo& info,
                         SimContext& ctx, Arena& arena) {
  auto vals = CollectVecElements(var_name, info, ctx, arena);
  auto order = IdentityOrder(vals.size());
  std::reverse(order.begin(), order.end());
  WriteVecElements(var_name, info, GatherByOrder(vals, order), ctx);
  ApplyDynArrayIdPermutation(var_name, info, order, ctx);
}

// §7.12.2 shuffle() randomizes the element order. The Fisher-Yates swaps are
// applied to the index vector rather than to the values, so the draw that
// produced the new order is also the permutation the element ids of a dynamic
// array follow under §7.10.3.
static void ArrayShuffle(std::string_view var_name, const ArrayInfo& info,
                         SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  auto order = IdentityOrder(vals.size());
  for (size_t i = order.size(); i > 1; --i) {
    size_t j = ctx.Urandom32() % i;
    std::swap(order[i - 1], order[j]);
  }
  WriteElements(var_name, info, GatherByOrder(vals, order), ctx, arena);
  ApplyDynArrayIdPermutation(var_name, info, order, ctx);
}

static bool IsOrderingMethod(std::string_view name) {
  return name == "sort" || name == "rsort" || name == "reverse" ||
         name == "shuffle";
}

// Validates the 'with'-clause usage for ordering methods. Returns true if
// execution should continue; sets *handled when the call has already been
// fully resolved (diagnostic emitted) and the caller should return *result.
static bool CheckOrderingWithClause(const MethodCallParts& parts,
                                    const Expr* expr, SimContext& ctx,
                                    bool& handled, bool& result) {
  handled = false;
  result = false;
  if (!expr->args.empty() && !expr->with_expr) {
    ctx.GetDiag().Error(expr->args.front()->range.start,
                        "iterator argument without 'with' clause",
                        Subclause("7.12"));
    handled = true;
    result = false;
    return false;
  }
  if ((parts.method_name == "reverse" || parts.method_name == "shuffle") &&
      expr->with_expr) {
    ctx.GetDiag().Error(expr->with_expr->range.start,
                        "'" + std::string(parts.method_name) +
                            "' does not accept a 'with' clause",
                        Subclause("7.12.2"));
    handled = true;
    result = true;
    return false;
  }
  return true;
}

static void ExecOrderingMethod(const MethodCallParts& parts,
                               const ArrayInfo& info, const Expr* expr,
                               SimContext& ctx, Arena& arena) {
  ArrayCtx ac{parts.var_name, info, ctx, arena};
  if (parts.method_name == "sort") {
    if (expr->with_expr)
      ArraySortWithExpr(ac, expr, true);
    else
      ArraySort(parts.var_name, info, ctx, arena);
    return;
  }
  if (parts.method_name == "rsort") {
    if (expr->with_expr)
      ArraySortWithExpr(ac, expr, false);
    else
      ArrayRsort(parts.var_name, info, ctx, arena);
    return;
  }
  if (parts.method_name == "reverse") {
    ArrayReverse(parts.var_name, info, ctx, arena);
    return;
  }
  ArrayShuffle(parts.var_name, info, ctx, arena);
}

bool TryExecArrayMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  auto* info = ctx.FindArrayInfo(parts.var_name);
  if (!info) return false;
  if (!IsOrderingMethod(parts.method_name)) return false;

  bool handled = false;
  bool result = false;
  if (!CheckOrderingWithClause(parts, expr, ctx, handled, result)) {
    if (handled) return result;
  }

  ExecOrderingMethod(parts, *info, expr, ctx, arena);
  return true;
}

bool TryEvalArrayProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out) {
  ArrayInfo scratch;
  const auto* info = ArrayInfoForReduction(var_name, prop, ctx, scratch);
  if (!info) return false;
  ArrayCtx ac{var_name, *info, ctx, arena};
  if (DispatchReduction(prop, ac, out)) return true;
  return DispatchQuery(prop, ac, out);
}

bool TryExecArrayPropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena& arena) {
  auto* info = ctx.FindArrayInfo(var_name);
  if (!info) return false;
  if (prop == "sort") {
    ArraySort(var_name, *info, ctx, arena);
    return true;
  }
  if (prop == "rsort") {
    ArrayRsort(var_name, *info, ctx, arena);
    return true;
  }
  if (prop == "reverse") {
    ArrayReverse(var_name, *info, ctx, arena);
    return true;
  }
  if (prop == "shuffle") {
    ArrayShuffle(var_name, *info, ctx, arena);
    return true;
  }
  return false;
}

}  // namespace delta
