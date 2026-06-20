#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

static Logic4Vec NonexistentQueueElement(const QueueObject* q, Arena& arena) {
  // Empty queue: yield the value of a nonexistent element of the queue's
  // element type (Table 7-1, see 7.4.5) and leave the queue unchanged.
  return q->is_4state ? MakeAllX(arena, q->elem_width)
                      : MakeLogic4VecVal(arena, q->elem_width, 0);
}

static void PopQueueFront(QueueObject* q, Arena& arena, Logic4Vec& out) {
  if (q->elements.empty()) {
    out = NonexistentQueueElement(q, arena);
  } else {
    out = q->elements.front();
    q->elements.erase(q->elements.begin());
    if (!q->element_ids.empty()) q->element_ids.erase(q->element_ids.begin());
    ++q->generation;
  }
}

static void PopQueueBack(QueueObject* q, Arena& arena, Logic4Vec& out) {
  if (q->elements.empty()) {
    out = NonexistentQueueElement(q, arena);
  } else {
    out = q->elements.back();
    q->elements.pop_back();
    if (!q->element_ids.empty()) q->element_ids.pop_back();
    ++q->generation;
  }
}

static bool DispatchQueueEval(std::string_view method, QueueObject* q,
                              Arena& arena, Logic4Vec& out) {
  if (method == "size") {
    out = MakeLogic4VecVal(arena, 32, q->elements.size());
    return true;
  }
  if (method == "pop_front") {
    PopQueueFront(q, arena, out);
    return true;
  }
  if (method == "pop_back") {
    PopQueueBack(q, arena, out);
    return true;
  }
  return false;
}

static void QueuePushBack(QueueObject* q, const Expr* expr, SimContext& ctx,
                          Arena& arena) {
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
}

static void QueuePushFront(QueueObject* q, const Expr* expr, SimContext& ctx,
                           Arena& arena) {
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
}

static void QueueInsertAt(QueueObject* q, const Expr* expr, SimContext& ctx,
                          Arena& arena) {
  auto idx_val = EvalExpr(expr->args[0], ctx, arena);
  auto val = EvalExpr(expr->args[1], ctx, arena);
  if (!idx_val.IsKnown()) return;
  auto raw = static_cast<int64_t>(idx_val.ToUint64());
  if (idx_val.is_signed && raw < 0) return;
  auto idx = static_cast<size_t>(raw);
  if (idx <= q->elements.size()) {
    q->elements.insert(q->elements.begin() + static_cast<ptrdiff_t>(idx), val);
    q->element_ids.insert(q->element_ids.begin() + static_cast<ptrdiff_t>(idx),
                          q->AllocateId());
    if (q->max_size > 0 &&
        static_cast<int32_t>(q->elements.size()) > q->max_size) {
      q->elements.pop_back();
      q->element_ids.pop_back();
      ctx.GetDiag().Warning({}, "bounded queue overflow in insert");
    }
    ++q->generation;
  }
}

static bool DispatchQueuePush(std::string_view method, QueueObject* q,
                              const Expr* expr, SimContext& ctx, Arena& arena) {
  if (method == "push_back" && !expr->args.empty()) {
    QueuePushBack(q, expr, ctx, arena);
    return true;
  }
  if (method == "push_front" && !expr->args.empty()) {
    QueuePushFront(q, expr, ctx, arena);
    return true;
  }
  if (method == "insert" && expr->args.size() >= 2) {
    QueueInsertAt(q, expr, ctx, arena);
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

}  // namespace delta
