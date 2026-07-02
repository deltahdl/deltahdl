#include "simulator/eval_array.h"

#include <algorithm>
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

// The index-type spec of an associative array (§7.8): how an index expression
// is reduced to a stored key. Mirrors the AssocArrayObject index fields.
struct AssocKeySpec {
  uint32_t index_width = 64;
  bool is_wildcard = false;
  bool is_signed = true;
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

// Reduces the values produced by the with-clause expression of `expr` for each
// element of the named array (§7.12.3). `method` selects the fold and is passed
// explicitly so this serves both the parenthesized call form (method name on
// expr->lhs->rhs) and the bare member-access form `arr.sum with (e)` (method
// name on expr->rhs). The result takes the width of the with expression.
static Logic4Vec ReduceWithExpr(std::string_view var_name,
                                const ArrayInfo& info, const Expr* expr,
                                std::string_view method, SimContext& ctx,
                                Arena& arena) {
  auto elems = CollectVecElements(var_name, info, ctx, arena);
  auto names = ExtractIterNames(expr);
  WithIterEnv env{names.iter_name, names.idx_var_name, ctx, arena};

  uint32_t result_width = 0;
  auto vals = EvalReduceWithValues(elems, expr, env, result_width);
  if (result_width == 0) result_width = info.elem_width;

  uint64_t result = ApplyReduction(method, vals);
  return MakeLogic4VecVal(arena, result_width, result);
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

struct ArrayCtx {
  std::string_view var_name;
  const ArrayInfo& info;
  SimContext& ctx;
  Arena& arena;
};

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
// bare property form). Returns false for non-reduction methods so the caller
// keeps handling its own methods (size, exists, traversal, …).
static bool TryAssocReduction(AssocArrayObject* aa, std::string_view method,
                              const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out) {
  if (!IsReductionMethod(method)) return false;
  auto elems = CollectAssocElements(aa);
  if (expr != nullptr && expr->with_expr != nullptr) {
    auto names = ExtractIterNames(expr);
    WithIterEnv env{names.iter_name, names.idx_var_name, ctx, arena};
    uint32_t result_width = 0;
    auto vals = EvalReduceWithValues(elems, expr, env, result_width);
    if (result_width == 0) result_width = aa->elem_width;
    out = MakeLogic4VecVal(arena, result_width, ApplyReduction(method, vals));
    return true;
  }
  std::vector<uint64_t> vals;
  vals.reserve(elems.size());
  for (const auto& e : elems) vals.push_back(e.ToUint64());
  out = MakeLogic4VecVal(arena, aa->elem_width, ApplyReduction(method, vals));
  return true;
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
    out = ReduceWithExpr(ac.var_name, ac.info, expr, method, ac.ctx, ac.arena);
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
    out = ReduceWithExpr(var_name, *info, expr, method, ctx, arena);
    return true;
  }
  if (auto* aa = ctx.FindAssocArray(var_name))
    return TryAssocReduction(aa, method, expr, ctx, arena, out);
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
}

static void ArraySort(std::string_view var_name, const ArrayInfo& info,
                      SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  std::sort(vals.begin(), vals.end());
  WriteElements(var_name, info, vals, ctx, arena);
}

static void ArrayRsort(std::string_view var_name, const ArrayInfo& info,
                       SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  std::sort(vals.begin(), vals.end(), std::greater<>());
  WriteElements(var_name, info, vals, ctx, arena);
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

static void ArrayReverse(std::string_view var_name, const ArrayInfo& info,
                         SimContext& ctx, Arena& arena) {
  auto vals = CollectVecElements(var_name, info, ctx, arena);
  std::reverse(vals.begin(), vals.end());
  WriteVecElements(var_name, info, vals, ctx);
}

static void ArrayShuffle(std::string_view var_name, const ArrayInfo& info,
                         SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);

  for (size_t i = vals.size(); i > 1; --i) {
    size_t j = ctx.Urandom32() % i;
    std::swap(vals[i - 1], vals[j]);
  }
  WriteElements(var_name, info, vals, ctx, arena);
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
    ctx.GetDiag().Error({}, "iterator argument without 'with' clause");
    handled = true;
    result = false;
    return false;
  }
  if ((parts.method_name == "reverse" || parts.method_name == "shuffle") &&
      expr->with_expr) {
    ctx.GetDiag().Error({}, "'" + std::string(parts.method_name) +
                                "' does not accept a 'with' clause");
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

static std::string Vec2Str(const Logic4Vec& vec) {
  uint32_t nbytes = vec.width / 8;
  std::string result;
  result.reserve(nbytes);
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    auto ch = static_cast<char>((vec.words[word].aval >> bit) & 0xFF);
    if (ch != 0) result.push_back(ch);
  }
  return result;
}

static Logic4Vec Str2Vec(const std::string& s, Arena& arena) {
  uint32_t w = static_cast<uint32_t>(s.size()) * 8;
  if (w == 0) w = 8;
  auto vec = MakeLogic4Vec(arena, w);
  for (size_t i = 0; i < s.size(); ++i) {
    auto byte_idx = static_cast<uint32_t>(s.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    vec.words[word].aval |= static_cast<uint64_t>(s[i]) << bit;
  }
  return vec;
}

static std::string EvalStrKey(const Expr* expr, SimContext& ctx, Arena& arena) {
  return Vec2Str(EvalExpr(expr, ctx, arena));
}

static int64_t EvalIntKey(const Expr* expr, SimContext& ctx, Arena& arena,
                          const AssocKeySpec& spec = {}) {
  auto val = EvalExpr(expr, ctx, arena);
  if (HasUnknownBits(val)) {
    ctx.GetDiag().Warning({}, "associative array index contains x/z");
  }
  return AssocIntKey(val, spec.is_wildcard, spec.index_width, spec.is_signed);
}

static bool AssocExists(AssocArrayObject* aa, const Expr* expr, SimContext& ctx,
                        Arena& arena, Logic4Vec& out) {
  if (expr->args.empty()) return false;
  uint64_t found = 0;
  if (aa->is_string_key) {
    found = aa->str_data.count(EvalStrKey(expr->args[0], ctx, arena)) ? 1 : 0;
  } else {
    found = aa->int_data.count(EvalIntKey(
                expr->args[0], ctx, arena,
                {aa->index_width, aa->is_wildcard, aa->is_index_signed}))
                ? 1
                : 0;
  }
  out = MakeLogic4VecVal(arena, 32, found);
  return true;
}

static bool AssocStrTraversal(AssocArrayObject* aa, std::string_view method,
                              Variable* ref_var, Arena& arena, Logic4Vec& out) {
  auto& m = aa->str_data;
  if (m.empty()) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }
  if (method == "first") {
    ref_var->value = Str2Vec(m.begin()->first, arena);
    out = MakeLogic4VecVal(arena, 32, 1);
    return true;
  }
  if (method == "last") {
    ref_var->value = Str2Vec(m.rbegin()->first, arena);
    out = MakeLogic4VecVal(arena, 32, 1);
    return true;
  }
  auto cur_key = Vec2Str(ref_var->value);
  if (method == "next") {
    // §7.9.6 — next() yields the smallest index strictly greater than the
    // argument value. The argument need not itself be a stored index, so
    // compare by value rather than locating an existing entry first.
    auto it = m.upper_bound(cur_key);
    if (it == m.end()) {
      out = MakeLogic4VecVal(arena, 32, 0);
      return true;
    }
    ref_var->value = Str2Vec(it->first, arena);
    out = MakeLogic4VecVal(arena, 32, 1);
    return true;
  }
  // §7.9.7 — prev() yields the largest index strictly smaller than the
  // argument value. The argument need not itself be a stored index, so locate
  // the lower bound by value and step back to its predecessor.
  auto it = m.lower_bound(cur_key);
  if (it == m.begin()) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }
  --it;
  ref_var->value = Str2Vec(it->first, arena);
  out = MakeLogic4VecVal(arena, 32, 1);
  return true;
}

static int WriteTraversalKey(Variable* ref, int64_t key, uint32_t idx_width,
                             Arena& arena) {
  uint32_t w = ref->value.width;
  if (w == 0) w = 32;
  ref->value = MakeLogic4VecVal(arena, w, static_cast<uint64_t>(key));
  return (w < idx_width) ? -1 : 1;
}

static bool AssocIntTraversal(AssocArrayObject* aa, std::string_view method,
                              Variable* ref_var, Arena& arena, Logic4Vec& out) {
  auto& m = aa->int_data;
  if (m.empty()) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }
  if (method == "first") {
    auto r =
        WriteTraversalKey(ref_var, m.begin()->first, aa->index_width, arena);
    out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(r));
    return true;
  }
  if (method == "last") {
    auto r =
        WriteTraversalKey(ref_var, m.rbegin()->first, aa->index_width, arena);
    out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(r));
    return true;
  }
  auto cur_key = static_cast<int64_t>(ref_var->value.ToUint64());
  if (method == "next") {
    // §7.9.6 — next() yields the smallest index strictly greater than the
    // argument value. The argument need not itself be a stored index, so
    // compare by value rather than locating an existing entry first.
    auto it = m.upper_bound(cur_key);
    if (it == m.end()) {
      out = MakeLogic4VecVal(arena, 32, 0);
      return true;
    }
    auto r = WriteTraversalKey(ref_var, it->first, aa->index_width, arena);
    out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(r));
    return true;
  }
  // §7.9.7 — prev() yields the largest index strictly smaller than the
  // argument value. The argument need not itself be a stored index, so locate
  // the lower bound by value and step back to its predecessor.
  auto it = m.lower_bound(cur_key);
  if (it == m.begin()) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }
  --it;
  auto r = WriteTraversalKey(ref_var, it->first, aa->index_width, arena);
  out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(r));
  return true;
}

static Variable* ResolveTraversalRef(const Expr* expr, SimContext& ctx) {
  if (expr->args.empty()) return nullptr;
  auto* ref_expr = expr->args[0];
  if (ref_expr->kind != ExprKind::kIdentifier) return nullptr;
  return ctx.FindVariable(ref_expr->text);
}

static bool AssocTraversal(AssocArrayObject* aa, std::string_view method,
                           Variable* ref_var, Arena& arena, Logic4Vec& out) {
  if (aa->is_string_key)
    return AssocStrTraversal(aa, method, ref_var, arena, out);
  return AssocIntTraversal(aa, method, ref_var, arena, out);
}

bool TryEvalAssocMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  auto* aa = ctx.FindAssocArray(parts.var_name);
  if (!aa) return false;
  if (parts.method_name == "size" || parts.method_name == "num") {
    out = MakeLogic4VecVal(arena, 32, aa->Size());
    return true;
  }
  if (parts.method_name == "exists")
    return AssocExists(aa, expr, ctx, arena, out);
  if (parts.method_name == "delete") {
    TryExecAssocMethodStmt(expr, ctx, arena);
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (parts.method_name == "first" || parts.method_name == "last" ||
      parts.method_name == "next" || parts.method_name == "prev") {
    auto* ref_var = ResolveTraversalRef(expr, ctx);
    if (!ref_var) {
      out = MakeLogic4VecVal(arena, 32, 0);
      return true;
    }
    return AssocTraversal(aa, parts.method_name, ref_var, arena, out);
  }
  return TryAssocReduction(aa, parts.method_name, expr, ctx, arena, out);
}

static bool ExecAssocDelete(AssocArrayObject* aa, const Expr* expr,
                            SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) {
    aa->int_data.clear();
    aa->str_data.clear();
    return true;
  }
  if (aa->is_string_key) {
    aa->str_data.erase(EvalStrKey(expr->args[0], ctx, arena));
  } else {
    aa->int_data.erase(
        EvalIntKey(expr->args[0], ctx, arena,
                   {aa->index_width, aa->is_wildcard, aa->is_index_signed}));
  }
  return true;
}

bool TryExecAssocMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  auto* aa = ctx.FindAssocArray(parts.var_name);
  if (!aa) return false;
  if (parts.method_name == "delete")
    return ExecAssocDelete(aa, expr, ctx, arena);
  return false;
}

bool TryEvalAssocProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out) {
  auto* aa = ctx.FindAssocArray(var_name);
  if (!aa) return false;
  if (prop == "size" || prop == "num") {
    out = MakeLogic4VecVal(arena, 32, aa->Size());
    return true;
  }
  return TryAssocReduction(aa, prop, nullptr, ctx, arena, out);
}

bool TryExecAssocPropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena&) {
  auto* aa = ctx.FindAssocArray(var_name);
  if (!aa) return false;
  if (prop == "delete") {
    aa->int_data.clear();
    aa->str_data.clear();
    return true;
  }
  return false;
}

}  // namespace delta
