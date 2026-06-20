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

static Logic4Vec ReduceWithExpr(std::string_view var_name,
                                const ArrayInfo& info, const Expr* expr,
                                SimContext& ctx, Arena& arena) {
  auto elems = CollectVecElements(var_name, info, ctx, arena);
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

  std::vector<uint64_t> vals;
  vals.reserve(elems.size());
  uint32_t result_width = 0;
  for (size_t i = 0; i < elems.size(); ++i) {
    ctx.PushScope();
    auto* item_var = ctx.CreateLocalVariable(iter_name, elems[i].width);
    item_var->value = elems[i];
    auto* idx_var = ctx.CreateLocalVariable(idx_var_name, 32);
    idx_var->value = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(i));
    Logic4Vec ev = EvalExpr(expr->with_expr, ctx, arena);
    ctx.PopScope();
    vals.push_back(ev.ToUint64());
    if (i == 0) result_width = ev.width;
  }
  if (result_width == 0) result_width = info.elem_width;

  std::string_view method = expr->lhs->rhs->text;

  uint64_t result = 0;
  if (method == "sum") {
    for (auto v : vals) result += v;
  } else if (method == "product") {
    result = 1;
    for (auto v : vals) result *= v;
  } else if (method == "and") {
    result = vals.empty() ? 0 : vals[0];
    for (size_t i = 1; i < vals.size(); ++i) result &= vals[i];
  } else if (method == "or") {
    for (auto v : vals) result |= v;
  } else if (method == "xor") {
    for (auto v : vals) result ^= v;
  }
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
    out = ReduceWithExpr(ac.var_name, ac.info, expr, ac.ctx, ac.arena);
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
  auto* info = ctx.FindArrayInfo(parts.var_name);
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

static uint64_t EvalSortKey(const Expr* with_expr, std::string_view iter_name,
                            const std::string& idx_var_name,
                            const Logic4Vec& elem, size_t index,
                            SimContext& ctx, Arena& arena) {
  ctx.PushScope();
  auto* item_var = ctx.CreateLocalVariable(iter_name, elem.width);
  item_var->value = elem;
  auto* idx_var = ctx.CreateLocalVariable(idx_var_name, 32);
  idx_var->value = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(index));
  uint64_t key = EvalExpr(with_expr, ctx, arena).ToUint64();
  ctx.PopScope();
  return key;
}

static void ArraySortWithExpr(std::string_view var_name, const ArrayInfo& info,
                              const Expr* expr, bool ascending, SimContext& ctx,
                              Arena& arena) {
  auto vals = CollectVecElements(var_name, info, ctx, arena);
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

  std::vector<std::pair<uint64_t, size_t>> keys(vals.size());
  for (size_t i = 0; i < vals.size(); ++i) {
    keys[i] = {EvalSortKey(expr->with_expr, iter_name, idx_var_name, vals[i], i,
                           ctx, arena),
               i};
  }
  if (ascending) {
    std::sort(keys.begin(), keys.end());
  } else {
    std::sort(keys.begin(), keys.end(),
              [](const auto& a, const auto& b) { return a.first > b.first; });
  }
  std::vector<Logic4Vec> sorted(vals.size());
  for (size_t i = 0; i < keys.size(); ++i) sorted[i] = vals[keys[i].second];
  WriteVecElements(var_name, info, sorted, ctx);
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

bool TryExecArrayMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  auto* info = ctx.FindArrayInfo(parts.var_name);
  if (!info) return false;
  if (!IsOrderingMethod(parts.method_name)) return false;

  if (!expr->args.empty() && !expr->with_expr) {
    ctx.GetDiag().Error({}, "iterator argument without 'with' clause");
    return false;
  }

  if ((parts.method_name == "reverse" || parts.method_name == "shuffle") &&
      expr->with_expr) {
    ctx.GetDiag().Error({}, "'" + std::string(parts.method_name) +
                                "' does not accept a 'with' clause");
    return true;
  }
  if (parts.method_name == "sort") {
    if (expr->with_expr)
      ArraySortWithExpr(parts.var_name, *info, expr, true, ctx, arena);
    else
      ArraySort(parts.var_name, *info, ctx, arena);
    return true;
  }
  if (parts.method_name == "rsort") {
    if (expr->with_expr)
      ArraySortWithExpr(parts.var_name, *info, expr, false, ctx, arena);
    else
      ArrayRsort(parts.var_name, *info, ctx, arena);
    return true;
  }
  if (parts.method_name == "reverse") {
    ArrayReverse(parts.var_name, *info, ctx, arena);
    return true;
  }
  if (parts.method_name == "shuffle") {
    ArrayShuffle(parts.var_name, *info, ctx, arena);
    return true;
  }
  return false;
}

bool TryEvalArrayProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out) {
  auto* info = ctx.FindArrayInfo(var_name);
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
                          uint32_t index_width = 64, bool is_wildcard = false,
                          bool is_signed = true) {
  auto val = EvalExpr(expr, ctx, arena);
  if (HasUnknownBits(val)) {
    ctx.GetDiag().Warning({}, "associative array index contains x/z");
  }
  return AssocIntKey(val, is_wildcard, index_width, is_signed);
}

static bool AssocExists(AssocArrayObject* aa, const Expr* expr, SimContext& ctx,
                        Arena& arena, Logic4Vec& out) {
  if (expr->args.empty()) return false;
  uint64_t found = 0;
  if (aa->is_string_key) {
    found = aa->str_data.count(EvalStrKey(expr->args[0], ctx, arena)) ? 1 : 0;
  } else {
    found = aa->int_data.count(EvalIntKey(expr->args[0], ctx, arena,
                                          aa->index_width, aa->is_wildcard,
                                          aa->is_index_signed))
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
  return false;
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
    aa->int_data.erase(EvalIntKey(expr->args[0], ctx, arena, aa->index_width,
                                  aa->is_wildcard, aa->is_index_signed));
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
  return false;
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
