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
#include "simulator/assoc_index.h"
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
  std::string_view subarray_owner = {};
  const ArrayInfo* subarray_info = nullptr;
  const QueueObject* element_queue_owner = nullptr;
  uint32_t index_base = 0;
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
  DedupeLocatorResults(lc, false, out);
}

static void LocatorUniqueIndexWith(const LocatorCtx& lc,
                                   std::vector<Logic4Vec>& out) {
  DedupeLocatorResults(lc, true, out);
}

static bool ExtractLocatorParts(const Expr* expr, Arena& arena,
                                MethodCallParts& out) {
  if (expr->kind == ExprKind::kMemberAccess)
    return ExtractHandleAccessParts(expr, arena, out);
  return ExtractHandleMethodCallParts(expr, arena, out);
}

static const Expr* LocatorReceiver(const Expr* expr) {
  const Expr* access = expr->kind == ExprKind::kCall ? expr->lhs : expr;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution || access->rhs == nullptr ||
      access->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  return access->lhs;
}

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

struct AssocLocatorState {
  const std::vector<Logic4Vec>& keys;
  const std::vector<Logic4Vec>& vals;
  const LocatorCtx& lc;
  bool string_keys;
  SimContext& ctx;
  Arena& arena;

  Logic4Vec KeyVec(size_t i) const { return keys[i]; }
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
  Logic4Vec OrderValue(size_t i) const {
    return lc.with_expr ? EvalWith(i) : vals[i];
  }
};

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
    AssocScanForward(st, false, ProjectVal, out);
  } else if (method == "find_first") {
    AssocScanForward(st, true, ProjectVal, out);
  } else {
    AssocScanLast(st, ProjectVal, out);
  }
}

static void AssocLocatorFindIndex(std::string_view method,
                                  const AssocLocatorState& st,
                                  std::vector<Logic4Vec>& out) {
  if (method == "find_index") {
    AssocScanForward(st, false, ProjectKey, out);
  } else if (method == "find_first_index") {
    AssocScanForward(st, true, ProjectKey, out);
  } else {
    AssocScanLast(st, ProjectKey, out);
  }
}

static void AssocLocatorMinMax(std::string_view method,
                               const AssocLocatorState& st,
                               std::vector<Logic4Vec>& out) {
  const auto& vals = st.vals;
  if (vals.empty()) return;
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

static bool CheckAssocWithClauseRequired(std::string_view method,
                                         const Expr* expr, SimContext& ctx) {
  const bool kNeedsWith = method == "find" || method == "find_index" ||
                          method == "find_first" ||
                          method == "find_first_index" ||
                          method == "find_last" || method == "find_last_index";
  if (!expr->with_expr && kNeedsWith) {
    ctx.GetDiag().ErrorOnce(expr->range.start,
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
    keys.push_back(k.ToVec(arena, aa.index_width, aa.is_index_signed));
    vals.push_back(v);
    TakeElementSignedness(aa, vals.back());
  }
}

struct LocatorEnv {
  const Expr* expr;
  SimContext& ctx;
  Arena& arena;
};

struct IndexedLocatorInput {
  LocatorEnv env;
  const std::vector<Logic4Vec>& elems;
  bool is_str;
  std::string_view var_name;
  const ArrayInfo& info;
};

static const QueueObject* QueueOfQueuesNamed(std::string_view name,
                                             const ArrayInfo& info,
                                             SimContext& ctx) {
  if (!info.is_dynamic) return nullptr;
  const QueueObject* q = ctx.FindQueue(name);
  return q != nullptr && q->elements_are_queues ? q : nullptr;
}

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
  if (method == "map") return false;

  if (!CheckAssocWithClauseRequired(method, env.expr, env.ctx)) return false;

  std::vector<Logic4Vec> keys;
  std::vector<Logic4Vec> vals;
  CollectAssocKeyVals(aa, env.arena, keys, vals);

  LocatorCtx lc = MakeLocatorCtx(vals, false, env.expr, env.ctx, env.arena);
  AssocLocatorState st{keys, vals, lc, aa.is_string_key, env.ctx, env.arena};
  return DispatchAssocLocator(method, st, out);
}

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

static bool CheckIndexedWithClauseRequired(std::string_view method,
                                           const Expr* expr, SimContext& ctx) {
  if (method == "map" && !expr->with_expr) {
    ctx.GetDiag().ErrorOnce(expr->range.start,
                            "array method 'map' requires a 'with' clause",
                            Subclause("7.12.5"));
    return false;
  }

  if (!expr->with_expr) {
    if (method == "find" || method == "find_index" || method == "find_first" ||
        method == "find_first_index" || method == "find_last" ||
        method == "find_last_index") {
      ctx.GetDiag().ErrorOnce(expr->range.start,
                              "array locator method '" + std::string(method) +
                                  "' requires a 'with' clause",
                              Subclause("7.12.1"));
    }
    return false;
  }
  return true;
}

static bool DescribeQueueAsArray(std::string_view name, SimContext& ctx,
                                 ArrayInfo& queue_info) {
  auto* q = ctx.FindQueue(name);
  if (!q) return false;
  queue_info.is_dynamic = true;
  queue_info.elem_width = q->elem_width;
  return true;
}

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

static std::vector<Logic4Vec> SubarrayOffsets(size_t count, Arena& arena) {
  std::vector<Logic4Vec> offsets;
  offsets.reserve(count);
  for (size_t i = 0; i < count; ++i)
    offsets.push_back(MakeLogic4VecVal(arena, 32, i));
  return offsets;
}

static std::vector<Logic4Vec> LocatorElements(std::string_view name,
                                              const ArrayInfo& info,
                                              SimContext& ctx, Arena& arena) {
  if (HasSubarrayElements(info))
    return SubarrayOffsets(info.dim_sizes[0], arena);
  if (const QueueObject* q = QueueOfQueuesNamed(name, info, ctx))
    return SubarrayOffsets(q->elements.size(), arena);
  return CollectVecElements(name, info, ctx, arena);
}

static bool SubarrayLocatorParts(const Expr* expr, SimContext& ctx,
                                 Arena& arena, MethodCallParts& parts,
                                 ArrayInfo& sub) {
  const Expr* receiver = LocatorReceiver(expr);
  if (receiver == nullptr || receiver->kind != ExprKind::kSelect) return false;
  const Expr* access = expr->kind == ExprKind::kCall ? expr->lhs : expr;
  std::string prefix;
  if (!IsLocatorMethod(access->rhs->text) ||
      !ResolveSubarraySelect(receiver, ctx, arena, prefix, sub)) {
    return false;
  }
  parts.var_name = *arena.Create<std::string>(std::move(prefix));
  parts.method_name = access->rhs->text;
  return true;
}

static bool CollectLocatorResult(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::vector<Logic4Vec>& out) {
  MethodCallParts parts;
  ArrayInfo sub;
  AssocArrayObject* aa = LocatorAssocReceiver(expr, parts, ctx, arena);
  const bool kSubarray =
      aa == nullptr && SubarrayLocatorParts(expr, ctx, arena, parts, sub);
  if (aa == nullptr && !kSubarray && !ExtractLocatorParts(expr, arena, parts))
    return false;
  if (!IsLocatorMethod(parts.method_name)) return false;

  if (!expr->args.empty() && !expr->with_expr) {
    ctx.GetDiag().ErrorOnce(expr->args.front()->range.start,
                            "iterator argument without 'with' clause",
                            Subclause("7.12"));
    return false;
  }

  IteratorLayout layout(ExtractIterNames(expr).iter_name, parts.var_name, ctx);

  if (aa != nullptr)
    return TryCollectAssocLocatorResult(LocatorEnv{expr, ctx, arena}, parts,
                                        *aa, out);
  const ArrayInfo* info = kSubarray ? &sub : ctx.FindArrayInfo(parts.var_name);
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

static bool ReturnsElements(std::string_view method) {
  return method == "find" || method == "find_first" || method == "find_last" ||
         method == "min" || method == "max" || method == "unique";
}

bool TryCollectLocatorRows(const Expr* expr, SimContext& ctx, Arena& arena,
                           LocatorRows& out) {
  MethodCallParts parts;
  if (expr->with_expr == nullptr || !ExtractLocatorParts(expr, arena, parts) ||
      !ReturnsElements(parts.method_name))
    return false;
  const ArrayInfo* info = ctx.FindArrayInfo(parts.var_name);
  const QueueObject* queue = ctx.FindQueue(parts.var_name);
  bool rows_of_array = info != nullptr && HasSubarrayElements(*info);
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
    idx_var->value = key.ToVec(env.arena, kIw, aa.is_index_signed);
    Logic4Vec mapped = EvalExpr(lc.with_expr, ctx, env.arena);
    ctx.PopScope();
    out.int_data[key] = mapped;
    out.elem_width = mapped.width;
  }
}

bool TryCollectAssocMapResult(const Expr* expr, SimContext& ctx, Arena& arena,
                              AssocArrayObject& out) {
  MethodCallParts parts;
  auto* aa = LocatorAssocReceiver(expr, parts, ctx, arena);
  if (!aa) return false;
  if (parts.method_name != "map") return false;
  if (!expr->with_expr) {
    ctx.GetDiag().ErrorOnce(expr->range.start,
                            "array method 'map' requires a 'with' clause",
                            Subclause("7.12.5"));
    return false;
  }

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
    LocatorCtx lc = MakeLocatorCtx(vals, false, expr, ctx, arena);
    MapStringKeyedAssoc(LocatorEnv{expr, ctx, arena}, lc, *aa, out);
    return true;
  }

  vals.reserve(aa->int_data.size());
  for (const auto& [k, v] : aa->int_data) vals.push_back(v);
  LocatorCtx lc = MakeLocatorCtx(vals, false, expr, ctx, arena);
  MapIntKeyedAssoc(LocatorEnv{expr, ctx, arena}, lc, *aa, out);
  return true;
}

}  // namespace delta
