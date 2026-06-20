#include "simulator/eval_array.h"

#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

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

static std::vector<Logic4Vec> CollectVecElements(std::string_view var_name,
                                                 const ArrayInfo& info,
                                                 SimContext& ctx,
                                                 Arena& arena) {
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

static bool DispatchQueueEval(std::string_view method, QueueObject* q,
                              Arena& arena, Logic4Vec& out) {
  if (method == "size") {
    out = MakeLogic4VecVal(arena, 32, q->elements.size());
    return true;
  }
  if (method == "pop_front") {
    if (q->elements.empty()) {
      // Empty queue: yield the value of a nonexistent element of the queue's
      // element type (Table 7-1, see 7.4.5) and leave the queue unchanged.
      out = q->is_4state ? MakeAllX(arena, q->elem_width)
                         : MakeLogic4VecVal(arena, q->elem_width, 0);
    } else {
      out = q->elements.front();
      q->elements.erase(q->elements.begin());
      if (!q->element_ids.empty()) q->element_ids.erase(q->element_ids.begin());
      ++q->generation;
    }
    return true;
  }
  if (method == "pop_back") {
    if (q->elements.empty()) {
      // Empty queue: yield the value of a nonexistent element of the queue's
      // element type (Table 7-1, see 7.4.5) and leave the queue unchanged.
      out = q->is_4state ? MakeAllX(arena, q->elem_width)
                         : MakeLogic4VecVal(arena, q->elem_width, 0);
    } else {
      out = q->elements.back();
      q->elements.pop_back();
      if (!q->element_ids.empty()) q->element_ids.pop_back();
      ++q->generation;
    }
    return true;
  }
  return false;
}

static bool DispatchQueuePush(std::string_view method, QueueObject* q,
                              const Expr* expr, SimContext& ctx, Arena& arena) {
  if (method == "push_back" && !expr->args.empty()) {
    auto val = EvalExpr(expr->args[0], ctx, arena);
    bool has_room = (q->max_size < 0) ||
                    (static_cast<int32_t>(q->elements.size()) < q->max_size);
    if (has_room) {
      q->elements.push_back(val);
      q->element_ids.push_back(q->AllocateId());
      ++q->generation;
    } else {
      ctx.GetDiag().Warning({}, "bounded queue overflow in push_back");
    }
    return true;
  }
  if (method == "push_front" && !expr->args.empty()) {
    auto val = EvalExpr(expr->args[0], ctx, arena);
    q->elements.insert(q->elements.begin(), val);
    q->element_ids.insert(q->element_ids.begin(), q->AllocateId());
    if (q->max_size > 0 &&
        static_cast<int32_t>(q->elements.size()) > q->max_size) {
      q->elements.pop_back();
      q->element_ids.pop_back();
      ctx.GetDiag().Warning({}, "bounded queue overflow in push_front");
    }
    ++q->generation;
    return true;
  }
  if (method == "insert" && expr->args.size() >= 2) {
    auto idx_val = EvalExpr(expr->args[0], ctx, arena);
    auto val = EvalExpr(expr->args[1], ctx, arena);
    if (!idx_val.IsKnown()) return true;
    auto raw = static_cast<int64_t>(idx_val.ToUint64());
    if (idx_val.is_signed && raw < 0) return true;
    auto idx = static_cast<size_t>(raw);
    if (idx <= q->elements.size()) {
      q->elements.insert(q->elements.begin() + static_cast<ptrdiff_t>(idx),
                         val);
      q->element_ids.insert(
          q->element_ids.begin() + static_cast<ptrdiff_t>(idx),
          q->AllocateId());
      if (q->max_size > 0 &&
          static_cast<int32_t>(q->elements.size()) > q->max_size) {
        q->elements.pop_back();
        q->element_ids.pop_back();
        ctx.GetDiag().Warning({}, "bounded queue overflow in insert");
      }
      ++q->generation;
    }
    return true;
  }
  return false;
}

static bool DispatchQueueDelete(std::string_view method, QueueObject* q,
                                const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (method != "delete") return false;
  if (!expr->args.empty()) {
    auto idx_val = EvalExpr(expr->args[0], ctx, arena);
    if (!idx_val.IsKnown()) return true;
    auto raw = static_cast<int64_t>(idx_val.ToUint64());
    if (idx_val.is_signed && raw < 0) return true;
    auto idx = static_cast<size_t>(raw);
    if (idx < q->elements.size()) {
      q->elements.erase(q->elements.begin() + static_cast<ptrdiff_t>(idx));
      if (idx < q->element_ids.size())
        q->element_ids.erase(q->element_ids.begin() +
                             static_cast<ptrdiff_t>(idx));
      ++q->generation;
    }
  } else {
    q->elements.clear();
    q->element_ids.clear();
    ++q->generation;
  }
  return true;
}

static bool IsQueueMutator(std::string_view method) {
  return method == "push_back" || method == "push_front" ||
         method == "pop_back" || method == "pop_front" || method == "insert" ||
         method == "delete";
}

static void NotifyOwningVar(SimContext& ctx, std::string_view var_name) {
  if (auto* v = ctx.FindVariable(var_name)) v->NotifyWatchers();
}

bool TryEvalQueueMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  auto* q = ctx.FindQueue(parts.var_name);
  if (!q) return false;
  if (DispatchQueueEval(parts.method_name, q, arena, out)) {
    if (IsQueueMutator(parts.method_name)) NotifyOwningVar(ctx, parts.var_name);
    return true;
  }

  if (DispatchQueuePush(parts.method_name, q, expr, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    NotifyOwningVar(ctx, parts.var_name);
    return true;
  }
  if (DispatchQueueDelete(parts.method_name, q, expr, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    NotifyOwningVar(ctx, parts.var_name);
    return true;
  }
  return false;
}

bool TryExecQueueMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  auto* q = ctx.FindQueue(parts.var_name);
  if (!q) return false;
  if (DispatchQueuePush(parts.method_name, q, expr, ctx, arena)) {
    NotifyOwningVar(ctx, parts.var_name);
    return true;
  }
  if (DispatchQueueDelete(parts.method_name, q, expr, ctx, arena)) {
    NotifyOwningVar(ctx, parts.var_name);
    return true;
  }
  return false;
}

bool TryEvalQueueProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out) {
  auto* q = ctx.FindQueue(var_name);
  if (!q) return false;

  return DispatchQueueEval(prop, q, arena, out);
}

static void SortQueueWithIds(QueueObject* q, bool ascending) {
  auto& elems = q->elements;
  auto& ids = q->element_ids;
  std::vector<size_t> order(elems.size());
  for (size_t i = 0; i < order.size(); ++i) order[i] = i;
  std::sort(order.begin(), order.end(), [&](size_t a, size_t b) {
    return ascending ? elems[a].ToUint64() < elems[b].ToUint64()
                     : elems[a].ToUint64() > elems[b].ToUint64();
  });
  std::vector<Logic4Vec> sorted_elems(elems.size());
  std::vector<uint64_t> sorted_ids(ids.size());
  for (size_t i = 0; i < order.size(); ++i) {
    sorted_elems[i] = elems[order[i]];
    if (i < ids.size()) sorted_ids[i] = ids[order[i]];
  }
  elems = std::move(sorted_elems);
  ids = std::move(sorted_ids);
  ++q->generation;
}

static void ShuffleQueueWithIds(QueueObject* q, SimContext& ctx) {
  auto& elems = q->elements;
  auto& ids = q->element_ids;
  for (size_t i = elems.size(); i > 1; --i) {
    size_t j = ctx.Urandom32() % i;
    std::swap(elems[i - 1], elems[j]);
    if (i - 1 < ids.size() && j < ids.size()) std::swap(ids[i - 1], ids[j]);
  }
  ++q->generation;
}

bool TryExecQueuePropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena&) {
  auto* q = ctx.FindQueue(var_name);
  if (!q) return false;
  if (prop == "delete") {
    q->elements.clear();
    q->element_ids.clear();
    ++q->generation;
    return true;
  }
  if (prop == "sort") {
    SortQueueWithIds(q, true);
    return true;
  }
  if (prop == "rsort") {
    SortQueueWithIds(q, false);
    return true;
  }
  if (prop == "reverse") {
    std::reverse(q->elements.begin(), q->elements.end());
    std::reverse(q->element_ids.begin(), q->element_ids.end());
    ++q->generation;
    return true;
  }
  if (prop == "shuffle") {
    ShuffleQueueWithIds(q, ctx);
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

static bool IsStringArray(std::string_view var_name, const ArrayInfo& info,
                          SimContext& ctx) {
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
};

static LocatorCtx MakeLocatorCtx(const std::vector<Logic4Vec>& elems,
                                 bool is_str, const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
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
  std::string idx_var = std::string(iter_name) + "." + std::string(index_name);
  return LocatorCtx{elems, is_str,    expr->with_expr,   ctx,
                    arena, iter_name, std::move(idx_var)};
}

static bool EvalLocatorPredicate(const LocatorCtx& lc,
                                 const Logic4Vec& item_val, size_t item_index) {
  lc.ctx.PushScope();
  auto* item_var = lc.ctx.CreateLocalVariable(lc.iter_name, item_val.width);
  item_var->value = item_val;
  if (lc.is_string) lc.ctx.RegisterStringVariable(lc.iter_name);
  auto* idx_var = lc.ctx.CreateLocalVariable(lc.idx_var_name, 32);
  idx_var->value =
      MakeLogic4VecVal(lc.arena, 32, static_cast<uint64_t>(item_index));
  auto result = EvalExpr(lc.with_expr, lc.ctx, lc.arena).ToUint64();
  lc.ctx.PopScope();
  return result != 0;
}

static Logic4Vec EvalLocatorWithExpr(const LocatorCtx& lc,
                                     const Logic4Vec& item_val,
                                     size_t item_index) {
  lc.ctx.PushScope();
  auto* item_var = lc.ctx.CreateLocalVariable(lc.iter_name, item_val.width);
  item_var->value = item_val;
  if (lc.is_string) lc.ctx.RegisterStringVariable(lc.iter_name);
  auto* idx_var = lc.ctx.CreateLocalVariable(lc.idx_var_name, 32);
  idx_var->value =
      MakeLogic4VecVal(lc.arena, 32, static_cast<uint64_t>(item_index));
  auto result = EvalExpr(lc.with_expr, lc.ctx, lc.arena);
  lc.ctx.PopScope();
  return result;
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
  if (method == "find_last") {
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
  if (method == "find_last_index") {
    for (size_t i = lc.elems.size(); i > 0; --i) {
      if (!EvalLocatorPredicate(lc, lc.elems[i - 1], i - 1)) continue;
      out.push_back(
          MakeLogic4VecVal(lc.arena, 32, static_cast<uint64_t>(i - 1)));
      break;
    }
    return;
  }
  for (size_t i = 0; i < lc.elems.size(); ++i) {
    if (!EvalLocatorPredicate(lc, lc.elems[i], i)) continue;
    out.push_back(MakeLogic4VecVal(lc.arena, 32, static_cast<uint64_t>(i)));
    if (method == "find_first_index") break;
  }
}

static void LocatorMap(const LocatorCtx& lc, std::vector<Logic4Vec>& out) {
  for (size_t i = 0; i < lc.elems.size(); ++i) {
    lc.ctx.PushScope();
    auto* item_var =
        lc.ctx.CreateLocalVariable(lc.iter_name, lc.elems[i].width);
    item_var->value = lc.elems[i];
    if (lc.is_string) lc.ctx.RegisterStringVariable(lc.iter_name);
    auto* idx_var = lc.ctx.CreateLocalVariable(lc.idx_var_name, 32);
    idx_var->value = MakeLogic4VecVal(lc.arena, 32, static_cast<uint64_t>(i));
    out.push_back(EvalExpr(lc.with_expr, lc.ctx, lc.arena));
    lc.ctx.PopScope();
  }
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

static void LocatorUniqueIndex(const std::vector<Logic4Vec>& elems,
                               Arena& arena, std::vector<Logic4Vec>& out) {
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
      out.push_back(MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(i)));
    }
  }
}

static void LocatorMinMax(std::string_view method, const LocatorCtx& lc,
                          std::vector<Logic4Vec>& out) {
  if (lc.elems.empty()) return;
  size_t best_idx = 0;
  uint64_t best_val = lc.with_expr
                          ? EvalLocatorWithExpr(lc, lc.elems[0], 0).ToUint64()
                          : lc.elems[0].ToUint64();
  for (size_t i = 1; i < lc.elems.size(); ++i) {
    uint64_t val = lc.with_expr
                       ? EvalLocatorWithExpr(lc, lc.elems[i], i).ToUint64()
                       : lc.elems[i].ToUint64();
    if ((method == "min" && val < best_val) ||
        (method == "max" && val > best_val)) {
      best_val = val;
      best_idx = i;
    }
  }
  out.push_back(lc.elems[best_idx]);
}

static void LocatorUniqueWith(const LocatorCtx& lc,
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
      out.push_back(lc.elems[i]);
    }
  }
}

static void LocatorUniqueIndexWith(const LocatorCtx& lc,
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
      out.push_back(MakeLogic4VecVal(lc.arena, 32, static_cast<uint64_t>(i)));
    }
  }
}

static bool ExtractLocatorParts(const Expr* expr, MethodCallParts& out) {
  if (expr->kind == ExprKind::kMemberAccess) {
    if (!expr->lhs || expr->lhs->kind != ExprKind::kIdentifier) return false;
    if (!expr->rhs || expr->rhs->kind != ExprKind::kIdentifier) return false;
    out.var_name = expr->lhs->text;
    out.method_name = expr->rhs->text;
    return true;
  }

  return ExtractMethodCallParts(expr, out);
}

// §7.12.1 — array locator methods over an associative array. Two rules differ
// from the indexed-array case: index locators (find_index/.../unique_index)
// return a queue of the *index type* holding the matching keys rather than a
// queue of int holding 0-based positions; and "first"/"last" are the entries
// with the smallest/largest index (the first()/last() ordering of 7.9), which a
// std::map gives for free by visiting keys in ascending order. Only integer
// keys are representable through this value vector — string-keyed and wildcard
// arrays are left for the caller to handle.
static bool TryCollectAssocLocatorResult(const Expr* expr,
                                         const MethodCallParts& parts,
                                         AssocArrayObject& aa, SimContext& ctx,
                                         Arena& arena,
                                         std::vector<Logic4Vec>& out) {
  std::string_view method = parts.method_name;
  if (method == "map") return false;  // not a 7.12.1 locator method

  const bool needs_with = method == "find" || method == "find_index" ||
                          method == "find_first" ||
                          method == "find_first_index" ||
                          method == "find_last" || method == "find_last_index";
  if (!expr->with_expr && needs_with) {
    ctx.GetDiag().Error({}, "array locator method '" + std::string(method) +
                                "' requires a 'with' clause");
    return false;
  }
  if (aa.is_string_key) return false;  // index type not representable here

  std::vector<int64_t> keys;
  std::vector<Logic4Vec> vals;
  for (const auto& [k, v] : aa.int_data) {
    keys.push_back(k);
    vals.push_back(v);
  }

  LocatorCtx lc = MakeLocatorCtx(vals, /*is_str=*/false, expr, ctx, arena);
  const uint32_t iw = aa.index_width;
  auto key_vec = [&](size_t i) {
    return MakeLogic4VecVal(arena, iw, static_cast<uint64_t>(keys[i]));
  };
  // Evaluates the with expression for entry i, binding the element iterator to
  // the value and the index iterator to the key.
  auto eval_with = [&](size_t i) {
    ctx.PushScope();
    auto* item_var = ctx.CreateLocalVariable(lc.iter_name, vals[i].width);
    item_var->value = vals[i];
    auto* idx_var = ctx.CreateLocalVariable(lc.idx_var_name, iw);
    idx_var->value = key_vec(i);
    Logic4Vec r = EvalExpr(lc.with_expr, ctx, arena);
    ctx.PopScope();
    return r;
  };
  auto matches = [&](size_t i) { return eval_with(i).ToUint64() != 0; };
  auto sort_key = [&](size_t i) {
    return lc.with_expr ? eval_with(i).ToUint64() : vals[i].ToUint64();
  };

  if (method == "find") {
    for (size_t i = 0; i < vals.size(); ++i)
      if (matches(i)) out.push_back(vals[i]);
  } else if (method == "find_first") {
    for (size_t i = 0; i < vals.size(); ++i)
      if (matches(i)) {
        out.push_back(vals[i]);
        break;
      }
  } else if (method == "find_last") {
    for (size_t i = vals.size(); i > 0; --i)
      if (matches(i - 1)) {
        out.push_back(vals[i - 1]);
        break;
      }
  } else if (method == "find_index") {
    for (size_t i = 0; i < vals.size(); ++i)
      if (matches(i)) out.push_back(key_vec(i));
  } else if (method == "find_first_index") {
    for (size_t i = 0; i < vals.size(); ++i)
      if (matches(i)) {
        out.push_back(key_vec(i));
        break;
      }
  } else if (method == "find_last_index") {
    for (size_t i = vals.size(); i > 0; --i)
      if (matches(i - 1)) {
        out.push_back(key_vec(i - 1));
        break;
      }
  } else if (method == "min" || method == "max") {
    if (vals.empty()) return true;
    size_t best = 0;
    uint64_t best_key = sort_key(0);
    for (size_t i = 1; i < vals.size(); ++i) {
      uint64_t k = sort_key(i);
      if ((method == "min" && k < best_key) ||
          (method == "max" && k > best_key)) {
        best_key = k;
        best = i;
      }
    }
    out.push_back(vals[best]);
  } else if (method == "unique" || method == "unique_index") {
    std::vector<uint64_t> seen;
    for (size_t i = 0; i < vals.size(); ++i) {
      uint64_t v = sort_key(i);
      bool dup = false;
      for (uint64_t s : seen)
        if (s == v) {
          dup = true;
          break;
        }
      if (dup) continue;
      seen.push_back(v);
      out.push_back(method == "unique" ? vals[i] : key_vec(i));
    }
  } else {
    return false;
  }
  return true;
}

bool TryCollectLocatorResult(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::vector<Logic4Vec>& out) {
  MethodCallParts parts;
  if (!ExtractLocatorParts(expr, parts)) return false;
  if (!IsLocatorMethod(parts.method_name)) return false;

  if (!expr->args.empty() && !expr->with_expr) {
    ctx.GetDiag().Error({}, "iterator argument without 'with' clause");
    return false;
  }

  auto* info = ctx.FindArrayInfo(parts.var_name);
  if (!info) {
    // Associative arrays are stored separately and honor index-type returns
    // and key ordering through a dedicated path.
    if (auto* aa = ctx.FindAssocArray(parts.var_name))
      return TryCollectAssocLocatorResult(expr, parts, *aa, ctx, arena, out);
    return false;
  }

  auto elems = CollectVecElements(parts.var_name, *info, ctx, arena);
  bool is_str = IsStringArray(parts.var_name, *info, ctx);

  if (parts.method_name == "unique") {
    if (expr->with_expr) {
      LocatorCtx lc = MakeLocatorCtx(elems, is_str, expr, ctx, arena);
      LocatorUniqueWith(lc, out);
    } else {
      LocatorUnique(elems, arena, out);
    }
    return true;
  }
  if (parts.method_name == "unique_index") {
    if (expr->with_expr) {
      LocatorCtx lc = MakeLocatorCtx(elems, is_str, expr, ctx, arena);
      LocatorUniqueIndexWith(lc, out);
    } else {
      LocatorUniqueIndex(elems, arena, out);
    }
    return true;
  }
  if (parts.method_name == "min" || parts.method_name == "max") {
    LocatorCtx lc = MakeLocatorCtx(elems, is_str, expr, ctx, arena);
    LocatorMinMax(parts.method_name, lc, out);
    return true;
  }

  // §7.12.5 — map() replaces each element with the value of its with clause,
  // and that clause is required: there is nothing to evaluate without it, so a
  // bare map() is illegal rather than a silent no-op.
  if (parts.method_name == "map" && !expr->with_expr) {
    ctx.GetDiag().Error({}, "array method 'map' requires a 'with' clause");
    return false;
  }

  if (!expr->with_expr) {
    // §7.12.1 — the with clause is mandatory for the element- and
    // index-finding locators; it carries the Boolean predicate they filter on.
    // A bare find* call is illegal, so flag it instead of silently yielding
    // nothing.
    if (parts.method_name == "find" || parts.method_name == "find_index" ||
        parts.method_name == "find_first" ||
        parts.method_name == "find_first_index" ||
        parts.method_name == "find_last" ||
        parts.method_name == "find_last_index") {
      ctx.GetDiag().Error({}, "array locator method '" +
                                  std::string(parts.method_name) +
                                  "' requires a 'with' clause");
    }
    return false;
  }

  LocatorCtx lc = MakeLocatorCtx(elems, is_str, expr, ctx, arena);
  if (parts.method_name == "map") {
    LocatorMap(lc, out);
  } else if (parts.method_name == "find_index" ||
             parts.method_name == "find_first_index" ||
             parts.method_name == "find_last_index") {
    LocatorFindIndex(parts.method_name, lc, out);
  } else {
    LocatorFindDispatch(parts.method_name, lc, out);
  }
  return true;
}

// §7.12.5 — map() over an associative array. Unlike the locator methods, map
// does not collapse the array to a queue: it produces an associative array
// whose set of index values and index type match the source, with each stored
// value replaced by the value of the with expression. The with clause is
// required, and each result element takes the self-determined type of that
// expression (carried by the width of the evaluated value). Only the
// integer-keyed index type is representable through this path; string-keyed
// sources are left to the caller, mirroring the locator-result limitation.
bool TryCollectAssocMapResult(const Expr* expr, SimContext& ctx, Arena& arena,
                              AssocArrayObject& out) {
  MethodCallParts parts;
  if (!ExtractLocatorParts(expr, parts)) return false;
  if (parts.method_name != "map") return false;
  auto* aa = ctx.FindAssocArray(parts.var_name);
  if (!aa) return false;
  if (!expr->with_expr) {
    ctx.GetDiag().Error({}, "array method 'map' requires a 'with' clause");
    return false;
  }
  if (aa->is_string_key) return false;  // index type not representable here

  // The returned array's range and index type match the source: carry over the
  // index metadata and reuse the source keys unchanged.
  out.index_width = aa->index_width;
  out.is_index_signed = aa->is_index_signed;
  out.is_wildcard = aa->is_wildcard;
  out.is_string_key = false;
  out.int_data.clear();

  std::vector<int64_t> keys;
  std::vector<Logic4Vec> vals;
  for (const auto& [k, v] : aa->int_data) {
    keys.push_back(k);
    vals.push_back(v);
  }
  LocatorCtx lc = MakeLocatorCtx(vals, /*is_str=*/false, expr, ctx, arena);
  const uint32_t iw = aa->index_width;
  for (size_t i = 0; i < vals.size(); ++i) {
    ctx.PushScope();
    auto* item_var = ctx.CreateLocalVariable(lc.iter_name, vals[i].width);
    item_var->value = vals[i];
    auto* idx_var = ctx.CreateLocalVariable(lc.idx_var_name, iw);
    idx_var->value =
        MakeLogic4VecVal(arena, iw, static_cast<uint64_t>(keys[i]));
    Logic4Vec mapped = EvalExpr(lc.with_expr, ctx, arena);
    ctx.PopScope();
    out.int_data[keys[i]] = mapped;
    out.elem_width = mapped.width;
  }
  return true;
}

}  // namespace delta
