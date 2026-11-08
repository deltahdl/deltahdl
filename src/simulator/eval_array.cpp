#include "simulator/eval_array.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_array_element_queue.h"
#include "simulator/eval_array_internal.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

static void WriteVecElements(std::string_view var_name, const ArrayInfo& info,
                             const std::vector<Logic4Vec>& vals,
                             SimContext& ctx);

struct WithIterEnv {
  std::string_view iter_name;
  const std::string& idx_var_name;
  SimContext& ctx;
  Arena& arena;
  uint32_t index_base = 0;
  const std::vector<Logic4Vec>* keys = nullptr;
  bool string_keys = false;
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

static std::vector<size_t> IdentityOrder(size_t count) {
  std::vector<size_t> order(count);
  for (size_t i = 0; i < count; ++i) order[i] = i;
  return order;
}

template <typename T>
static std::vector<T> GatherByOrder(const std::vector<T>& vals,
                                    const std::vector<size_t>& order) {
  std::vector<T> out(order.size());
  for (size_t i = 0; i < order.size(); ++i) out[i] = vals[order[i]];
  return out;
}

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

static Logic4Vec ValueAsRead(const Variable& v) {
  Logic4Vec val = v.value;
  val.is_signed = v.is_signed;
  return val;
}

std::vector<Logic4Vec> CollectVecElements(std::string_view var_name,
                                          const ArrayInfo& info,
                                          SimContext& ctx, Arena& arena) {
  if (info.is_dynamic) {
    auto* q = ctx.FindQueue(var_name);
    if (!q) return {};
    std::vector<Logic4Vec> vals = q->elements;
    for (auto& v : vals) TakeElementSignedness(*q, v);
    return vals;
  }
  std::vector<Logic4Vec> vals;
  vals.reserve(info.size);
  for (uint32_t i = 0; i < info.size; ++i) {
    uint32_t idx = info.lo + i;
    auto name = std::string(var_name) + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(name);
    vals.push_back(v != nullptr ? ValueAsRead(*v)
                                : MakeLogic4VecVal(arena, info.elem_width, 0));
  }
  return vals;
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

IteratorLayout::IteratorLayout(std::string_view iter_name,
                               std::string_view array_name, SimContext& ctx)
    : ctx_(ctx), iter_name_(iter_name) {
  std::string_view type_name = ctx.VariableStructTypeName(array_name);
  if (type_name.empty()) return;
  previous_ = ctx.VariableStructTypeName(iter_name);
  ctx.SetVariableStructType(iter_name, type_name);
  bound_ = true;
}

IteratorLayout::~IteratorLayout() {
  if (bound_) ctx_.SetVariableStructType(iter_name_, previous_);
}

static Logic4Vec EvalWithExprForElement(const Expr* with_expr,
                                        const WithIterEnv& env,
                                        const Logic4Vec& elem, size_t index) {
  env.ctx.PushScope();
  auto* item_var =
      env.ctx.CreateLocalVariable(env.iter_name, elem.width, elem.is_signed);
  item_var->value = elem;
  Logic4Vec index_val =
      env.keys != nullptr
          ? (*env.keys)[index]
          : MakeLogic4VecVal(env.arena, 32, env.index_base + index);
  env.ctx.CreateLocalVariable(env.idx_var_name, index_val.width)->value =
      index_val;
  if (env.string_keys) env.ctx.RegisterStringVariable(env.idx_var_name);
  Logic4Vec ev = EvalExpr(with_expr, env.ctx, env.arena);
  env.ctx.PopScope();
  return ev;
}

struct WithResultType {
  uint32_t width = 0;
  bool is_signed = false;
};

static std::vector<uint64_t> EvalReduceWithValues(
    const std::vector<Logic4Vec>& elems, const Expr* expr,
    const WithIterEnv& env, WithResultType& type) {
  std::vector<uint64_t> vals;
  vals.reserve(elems.size());
  type = {};
  for (size_t i = 0; i < elems.size(); ++i) {
    Logic4Vec ev = EvalWithExprForElement(expr->with_expr, env, elems[i], i);
    vals.push_back(ev.ToUint64());
    if (i == 0) type = {ev.width, ev.is_signed};
  }
  return vals;
}

struct ArrayCtx {
  std::string_view var_name;
  const ArrayInfo& info;
  SimContext& ctx;
  Arena& arena;
};

static Logic4Vec EvalWithForRow(const ArrayCtx& ac, const Expr* expr,
                                const IterNames& names, uint32_t row) {
  SimContext& ctx = ac.ctx;
  ctx.PushScope();
  BindSubarrayIterator(SubarrayElement{ac.var_name, ac.info, row},
                       names.iter_name, ctx, ac.arena);
  ctx.CreateLocalVariable(names.idx_var_name, 32)->value =
      MakeLogic4VecVal(ac.arena, 32, ac.info.dim_los[0] + row);
  Logic4Vec value = EvalExpr(expr->with_expr, ctx, ac.arena);
  ctx.PopScope();
  return value;
}

static Logic4Vec ReduceRowsWithExpr(const ArrayCtx& ac, const Expr* expr,
                                    std::string_view method) {
  IterNames names = ExtractIterNames(expr);
  std::vector<uint64_t> vals;
  WithResultType type;
  for (uint32_t row = 0; row < ac.info.dim_sizes[0]; ++row) {
    Logic4Vec value = EvalWithForRow(ac, expr, names, row);
    if (row == 0) type = {value.width, value.is_signed};
    vals.push_back(value.ToUint64());
  }
  if (type.width == 0) type.width = ac.info.elem_width;
  Logic4Vec out =
      MakeLogic4VecVal(ac.arena, type.width, ApplyReduction(method, vals));
  out.is_signed = type.is_signed;
  return out;
}

static Logic4Vec ReduceWithExpr(const ArrayCtx& ac, const Expr* expr,
                                std::string_view method) {
  if (HasSubarrayElements(ac.info) && expr->with_expr != nullptr) {
    return ReduceRowsWithExpr(ac, expr, method);
  }
  auto elems = CollectVecElements(ac.var_name, ac.info, ac.ctx, ac.arena);
  auto names = ExtractIterNames(expr);
  WithIterEnv env{names.iter_name, names.idx_var_name, ac.ctx, ac.arena,
                  ac.info.lo};
  IteratorLayout layout(names.iter_name, ac.var_name, ac.ctx);

  WithResultType type;
  auto vals = EvalReduceWithValues(elems, expr, env, type);
  if (type.width == 0) type.width = ac.info.elem_width;

  uint64_t result = ApplyReduction(method, vals);
  Logic4Vec out = MakeLogic4VecVal(ac.arena, type.width, result);
  out.is_signed = type.is_signed;
  return out;
}

static Logic4Vec ArraySize(std::string_view var_name, SimContext& ctx,
                           Arena& arena) {
  auto* q = ctx.FindQueue(var_name);
  return MakeLogic4VecVal(arena, 32, q ? q->elements.size() : 0);
}

static Logic4Vec ArrayExtreme(std::string_view var_name, const ArrayInfo& info,
                              bool want_max, SimContext& ctx, Arena& arena) {
  auto vals = CollectVecElements(var_name, info, ctx, arena);
  if (vals.empty()) return MakeLogic4VecVal(arena, info.elem_width, 0);
  size_t best = 0;
  for (size_t i = 1; i < vals.size(); ++i) {
    const Logic4Vec& lower = want_max ? vals[best] : vals[i];
    const Logic4Vec& higher = want_max ? vals[i] : vals[best];
    if (OrdersBefore(lower, higher, vals[i].is_signed)) best = i;
  }
  return vals[best];
}

static bool IsReductionMethod(std::string_view method) {
  return method == "sum" || method == "product" || method == "and" ||
         method == "or" || method == "xor";
}

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

std::optional<Logic4Vec> TryAssocReduction(AssocArrayObject* aa,
                                           std::string_view method,
                                           const Expr* expr, SimContext& ctx,
                                           Arena& arena) {
  if (!IsReductionMethod(method)) return std::nullopt;
  std::vector<Logic4Vec> keys;
  std::vector<Logic4Vec> elems;
  CollectAssocKeyVals(*aa, arena, keys, elems);
  if (expr != nullptr && expr->with_expr != nullptr) {
    auto names = ExtractIterNames(expr);
    WithIterEnv env{names.iter_name, names.idx_var_name, ctx, arena};
    env.keys = &keys;
    env.string_keys = aa->is_string_key;
    WithResultType type;
    auto vals = EvalReduceWithValues(elems, expr, env, type);
    if (type.width == 0) type.width = aa->elem_width;
    Logic4Vec out =
        MakeLogic4VecVal(arena, type.width, ApplyReduction(method, vals));
    out.is_signed = type.is_signed;
    return out;
  }
  std::vector<uint64_t> vals;
  vals.reserve(elems.size());
  for (const auto& e : elems) vals.push_back(e.ToUint64());
  Logic4Vec out =
      MakeLogic4VecVal(arena, aa->elem_width, ApplyReduction(method, vals));
  out.is_signed = aa->is_signed;
  return out;
}

static bool ElementsAreSigned(const ArrayCtx& ac) {
  if (ac.info.is_dynamic) {
    const QueueObject* q = ac.ctx.FindQueue(ac.var_name);
    return q != nullptr && q->is_signed;
  }
  const Variable* first = ac.ctx.FindVariable(std::string(ac.var_name) + "[" +
                                              std::to_string(ac.info.lo) + "]");
  return first != nullptr && first->is_signed;
}

static Logic4Vec ReduceElements(std::string_view method, const ArrayCtx& ac) {
  Logic4Vec out = MakeLogic4VecVal(
      ac.arena, ac.info.elem_width,
      ApplyReduction(method, CollectElements(ac.var_name, ac.info, ac.ctx)));
  out.is_signed = ElementsAreSigned(ac);
  return out;
}

static bool DispatchReduction(std::string_view method, const ArrayCtx& ac,
                              Logic4Vec& out) {
  if (!IsReductionMethod(method)) return false;
  out = ReduceElements(method, ac);
  return true;
}

static bool DispatchReductionExpr(std::string_view method, const ArrayCtx& ac,
                                  const Expr* expr, Logic4Vec& out) {
  if (!IsReductionMethod(method)) return false;
  out = expr->with_expr ? ReduceWithExpr(ac, expr, method)
                        : ReduceElements(method, ac);
  return true;
}

static bool DispatchQuery(std::string_view method, const ArrayCtx& ac,
                          Logic4Vec& out) {
  if (method == "size") {
    out = ArraySize(ac.var_name, ac.ctx, ac.arena);
    return true;
  }
  if (method == "min" || method == "max") {
    out = ArrayExtreme(ac.var_name, ac.info, method == "max", ac.ctx, ac.arena);
    return true;
  }
  return false;
}

static bool TryStructArrayMemberMethod(const Expr* expr, SimContext& ctx,
                                       Arena& arena, Logic4Vec& out) {
  const Expr* access = expr->lhs;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->rhs == nullptr || expr->with_expr != nullptr)
    return false;
  std::string_view method = access->rhs->text;
  if (!IsReductionMethod(method)) return false;
  const StructFieldInfo* member = ResolveStructArrayMember(access->lhs, ctx);
  if (member == nullptr) return false;
  Logic4Vec whole = EvalExpr(access->lhs, ctx, arena);
  uint32_t ew = member->width / member->elem_count;
  std::vector<uint64_t> vals;
  vals.reserve(member->elem_count);
  for (uint32_t i = 0; i < member->elem_count; ++i) {
    vals.push_back(
        ExtractBitField(arena, whole, (member->elem_count - 1 - i) * ew, ew)
            .ToUint64());
  }
  out = MakeLogic4VecVal(arena, ew, ApplyReduction(method, vals));
  out.is_signed = member->is_signed;
  return true;
}

static bool TryQueuePropertyReduction(const Expr* expr, SimContext& ctx,
                                      Arena& arena, Logic4Vec& out) {
  const Expr* access = expr->lhs;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->rhs == nullptr || !IsReductionMethod(access->rhs->text)) {
    return false;
  }
  QueuePropertyReceiver receiver(expr, ctx, arena);
  return receiver.Call() != nullptr &&
         TryEvalArrayMethodCall(receiver.Call(), ctx, arena, out);
}

static bool TrySubarrayReduction(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  const Expr* access = expr->lhs;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->rhs == nullptr || !IsReductionMethod(access->rhs->text))
    return false;
  std::string prefix;
  ArrayInfo sub;
  if (!ResolveSubarraySelect(access->lhs, ctx, arena, prefix, sub))
    return false;
  ArrayCtx ac{prefix, sub, ctx, arena};
  return DispatchReductionExpr(access->rhs->text, ac, expr, out);
}

static bool TryElementQueueReduction(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  const Expr* access = expr->lhs;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->rhs == nullptr || !IsReductionMethod(access->rhs->text))
    return false;
  const QueueObject* q = ElementQueueOfSelect(access->lhs, ctx, arena, false);
  if (q == nullptr || q->elements_are_queues) return false;
  std::vector<Logic4Vec> elems = q->elements;
  for (Logic4Vec& e : elems) TakeElementSignedness(*q, e);
  std::string_view method = access->rhs->text;
  if (expr->with_expr == nullptr) {
    std::vector<uint64_t> vals;
    vals.reserve(elems.size());
    for (const Logic4Vec& e : elems) vals.push_back(e.ToUint64());
    out = MakeLogic4VecVal(arena, q->elem_width, ApplyReduction(method, vals));
    out.is_signed = q->is_signed;
    return true;
  }
  IterNames names = ExtractIterNames(expr);
  WithIterEnv env{names.iter_name, names.idx_var_name, ctx, arena};
  WithResultType type;
  std::vector<uint64_t> vals = EvalReduceWithValues(elems, expr, env, type);
  if (type.width == 0) type.width = q->elem_width;
  out = MakeLogic4VecVal(arena, type.width, ApplyReduction(method, vals));
  out.is_signed = type.is_signed;
  return true;
}

bool TryEvalArrayMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out) {
  if (TryStructArrayMemberMethod(expr, ctx, arena, out)) return true;
  if (TrySubarrayReduction(expr, ctx, arena, out)) return true;
  if (TryElementQueueReduction(expr, ctx, arena, out)) return true;
  MethodCallParts parts;
  if (!ExtractHandleMethodCallParts(expr, arena, parts))
    return TryQueuePropertyReduction(expr, ctx, arena, out);
  ArrayInfo scratch;
  const auto* info =
      ArrayInfoForReduction(parts.var_name, parts.method_name, ctx, scratch);
  if (!info) return TryQueuePropertyReduction(expr, ctx, arena, out);
  ArrayCtx ac{parts.var_name, *info, ctx, arena};
  if (DispatchReductionExpr(parts.method_name, ac, expr, out)) return true;
  if (DispatchQuery(parts.method_name, ac, out)) return true;

  if (TryExecArrayMethodStmt(expr, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  return false;
}

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

using SortKeys = std::vector<std::pair<Logic4Vec, size_t>>;

static SortKeys BuildSortKeys(const std::vector<Logic4Vec>& vals,
                              const Expr* expr, const WithIterEnv& env) {
  SortKeys keys(vals.size());
  for (size_t i = 0; i < vals.size(); ++i) {
    keys[i] = {EvalWithExprForElement(expr->with_expr, env, vals[i], i), i};
  }
  return keys;
}

static void SortKeysByValue(SortKeys& keys, bool ascending) {
  std::stable_sort(keys.begin(), keys.end(), [&](const auto& a, const auto& b) {
    return ascending ? OrdersBefore(a.first, b.first, a.first.is_signed)
                     : OrdersBefore(b.first, a.first, a.first.is_signed);
  });
}

static std::vector<Logic4Vec> ReorderByKeys(const std::vector<Logic4Vec>& vals,
                                            const SortKeys& keys) {
  std::vector<Logic4Vec> sorted(vals.size());
  for (size_t i = 0; i < keys.size(); ++i) sorted[i] = vals[keys[i].second];
  return sorted;
}

static void ArraySortWithExpr(const ArrayCtx& ac, const Expr* expr,
                              bool ascending) {
  auto vals = CollectVecElements(ac.var_name, ac.info, ac.ctx, ac.arena);
  auto names = ExtractIterNames(expr);
  WithIterEnv env{names.iter_name, names.idx_var_name, ac.ctx, ac.arena,
                  ac.info.lo};
  IteratorLayout layout(names.iter_name, ac.var_name, ac.ctx);
  auto keys = BuildSortKeys(vals, expr, env);
  SortKeysByValue(keys, ascending);
  std::vector<Logic4Vec> sorted = ReorderByKeys(vals, keys);
  WriteVecElements(ac.var_name, ac.info, sorted, ac.ctx);
  std::vector<size_t> order(keys.size());
  for (size_t i = 0; i < keys.size(); ++i) order[i] = keys[i].second;
  ApplyDynArrayIdPermutation(ac.var_name, ac.info, order, ac.ctx);
}

void SortQueueByWithExpr(QueueObject* q, const Expr* expr, bool ascending,
                         SimContext& ctx, Arena& arena) {
  auto names = ExtractIterNames(expr);
  WithIterEnv env{names.iter_name, names.idx_var_name, ctx, arena};
  std::vector<Logic4Vec> vals = q->elements;
  for (auto& v : vals) TakeElementSignedness(*q, v);
  SortKeys keys = BuildSortKeys(vals, expr, env);
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
    IteratorLayout layout(ExtractIterNames(expr).iter_name, var_name, ctx);
    SortQueueByWithExpr(q, expr, ascending, ctx, arena);
    return true;
  }
  return false;
}

static void ArraySortByValue(std::string_view var_name, const ArrayInfo& info,
                             bool ascending, SimContext& ctx, Arena& arena) {
  if (IsStringArray(var_name, info, ctx)) {
    auto elems = CollectVecElements(var_name, info, ctx, arena);
    std::vector<std::string> text;
    text.reserve(elems.size());
    for (const auto& e : elems) text.push_back(Logic4VecToString(e));
    auto order = IdentityOrder(elems.size());
    std::stable_sort(order.begin(), order.end(), [&](size_t a, size_t b) {
      return ascending ? text[a] < text[b] : text[a] > text[b];
    });
    WriteVecElements(var_name, info, GatherByOrder(elems, order), ctx);
    ApplyDynArrayIdPermutation(var_name, info, order, ctx);
    return;
  }
  auto vals = CollectVecElements(var_name, info, ctx, arena);
  auto order = IdentityOrder(vals.size());
  std::sort(order.begin(), order.end(), [&](size_t a, size_t b) {
    return ascending ? OrdersBefore(vals[a], vals[b], vals[a].is_signed)
                     : OrdersBefore(vals[b], vals[a], vals[a].is_signed);
  });
  WriteVecElements(var_name, info, GatherByOrder(vals, order), ctx);
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

static void ArrayReverse(std::string_view var_name, const ArrayInfo& info,
                         SimContext& ctx, Arena& arena) {
  auto vals = CollectVecElements(var_name, info, ctx, arena);
  auto order = IdentityOrder(vals.size());
  std::reverse(order.begin(), order.end());
  WriteVecElements(var_name, info, GatherByOrder(vals, order), ctx);
  ApplyDynArrayIdPermutation(var_name, info, order, ctx);
}

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

static bool CheckOrderingWithClause(const MethodCallParts& parts,
                                    const Expr* expr, SimContext& ctx,
                                    bool& handled, bool& result) {
  handled = false;
  result = false;
  if (!expr->args.empty() && !expr->with_expr) {
    ctx.GetDiag().ErrorOnce(expr->args.front()->range.start,
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
  if (!ExtractHandleMethodCallParts(expr, arena, parts)) return false;
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

bool CollectQueueOrAssocValues(std::string_view name, SimContext& ctx,
                               std::vector<Logic4Vec>& out) {
  if (const QueueObject* q = ctx.FindQueue(name)) {
    out.insert(out.end(), q->elements.begin(), q->elements.end());
    return true;
  }
  const AssocArrayObject* aa = ctx.FindAssocArray(name);
  if (aa == nullptr) return false;
  for (const auto& entry : aa->int_data) out.push_back(entry.second);
  for (const auto& entry : aa->str_data) out.push_back(entry.second);
  return true;
}

}  // namespace delta
