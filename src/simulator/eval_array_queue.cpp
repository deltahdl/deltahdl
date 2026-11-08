#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_event_property.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_array_element_queue.h"
#include "simulator/eval_array_internal.h"
#include "simulator/eval_class_sync.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/evaluation.h"
#include "simulator/queue_bound.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

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
    TakeElementSignedness(*q, out);
    return true;
  }
  if (method == "pop_back") {
    PopQueueBack(q, arena, out);
    TakeElementSignedness(*q, out);
    return true;
  }
  return false;
}

static const StructTypeInfo* QueueElementLayout(const Expr* call,
                                                SimContext& ctx) {
  const Expr* access = call->lhs;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->lhs == nullptr || access->lhs->kind != ExprKind::kIdentifier)
    return nullptr;
  return StructLayoutOfName(access->lhs->text, ctx);
}

static Logic4Vec PushedValue(QueueObject* q, const Expr* call, uint64_t id,
                             SimContext& ctx, Arena& arena) {
  const Expr* item = call->args.back();
  if (q->holds_events) return EventIdentityOf(item, ctx, arena);
  if (q->holds_class_handles) RecordContainedSyncHandle(item, ctx, arena);
  if (!q->elements_are_queues) {
    return OwnRhsWords(
        SizedForQueueElement(
            *q,
            EvalItemForLayout(item, QueueElementLayout(call, ctx), ctx, arena),
            arena),
        arena);
  }
  q->element_queues[id] = ElementQueueFromItem(q, item, ctx, arena);
  return NonexistentQueueElement(q, arena);
}

static void QueuePushBack(QueueObject* q, const Expr* expr, SimContext& ctx,
                          Arena& arena) {
  uint64_t id = q->AllocateId();
  q->elements.push_back(PushedValue(q, expr, id, ctx, arena));
  q->element_ids.push_back(id);
  ++q->generation;
  EnforceQueueBound(q, "push_back", expr->range.start, ctx);
}

static void QueuePushFront(QueueObject* q, const Expr* expr, SimContext& ctx,
                           Arena& arena) {
  uint64_t id = q->AllocateId();
  q->elements.insert(q->elements.begin(), PushedValue(q, expr, id, ctx, arena));
  q->element_ids.insert(q->element_ids.begin(), id);
  EnforceQueueBound(q, "push_front", expr->range.start, ctx);
  ++q->generation;
}

static void QueueInsertAt(QueueObject* q, const Expr* expr, SimContext& ctx,
                          Arena& arena) {
  auto idx_val = EvalExpr(expr->args[0], ctx, arena);
  if (!idx_val.IsKnown()) return;
  auto raw = static_cast<int64_t>(idx_val.ToUint64());
  if (idx_val.is_signed && raw < 0) return;
  auto idx = static_cast<size_t>(raw);
  if (idx <= q->elements.size()) {
    uint64_t id = q->AllocateId();
    Logic4Vec val = PushedValue(q, expr, id, ctx, arena);
    q->elements.insert(q->elements.begin() + static_cast<ptrdiff_t>(idx), val);
    q->element_ids.insert(q->element_ids.begin() + static_cast<ptrdiff_t>(idx),
                          id);
    EnforceQueueBound(q, "insert", expr->range.start, ctx);
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

static bool IsQueueOrderingMethod(std::string_view method) {
  return method == "sort" || method == "rsort" || method == "reverse" ||
         method == "shuffle";
}

void NotifyOwningVar(SimContext& ctx, std::string_view var_name) {
  if (auto* v = ctx.FindVariable(var_name)) v->NotifyWatchers();
}

struct QueueCall {
  QueueObject* queue = nullptr;
  const Expr* receiver = nullptr;
  std::string_view method;
  ClassObject* owner = nullptr;
};

static QueueCall ResolveQueueCall(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  QueueCall call;
  if (expr == nullptr || expr->lhs == nullptr ||
      expr->lhs->kind != ExprKind::kMemberAccess) {
    return call;
  }
  const Expr* access = expr->lhs;
  if (access->is_scope_resolution || access->lhs == nullptr ||
      access->rhs == nullptr || access->rhs->kind != ExprKind::kIdentifier) {
    return call;
  }
  call.receiver = access->lhs;
  call.method = access->rhs->text;
  bool writes =
      IsQueueMutator(call.method) || IsQueueOrderingMethod(call.method);
  if (access->lhs->kind == ExprKind::kSelect) {
    call.queue = ElementQueueOfSelect(access->lhs, ctx, arena, writes);
    if (call.queue != nullptr) return call;
  }
  call.queue = ResolveStructDynMember(access->lhs, ctx, arena, writes);
  if (call.queue != nullptr) return call;
  call.queue = FindQueueOfBase(access->lhs, ctx, arena, &call.owner);
  return call;
}

static bool OrderQueue(QueueObject* q, std::string_view prop, SimContext& ctx);

static bool ExecQueueOrdering(const QueueCall& call, const Expr* expr,
                              SimContext& ctx, Arena& arena) {
  if (expr->with_expr != nullptr &&
      (call.method == "sort" || call.method == "rsort")) {
    SortQueueByWithExpr(call.queue, expr, call.method == "sort", ctx, arena);
    return true;
  }
  return IsQueueOrderingMethod(call.method) &&
         OrderQueue(call.queue, call.method, ctx);
}

bool TryEvalQueueMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out) {
  QueueCall call = ResolveQueueCall(expr, ctx, arena);
  if (call.queue == nullptr) return false;
  if (DispatchQueueEval(call.method, call.queue, arena, out)) {
    if (IsQueueMutator(call.method))
      AnnounceQueueChange(call.receiver, call.owner, ctx);
    return true;
  }

  if (DispatchQueuePush(call.method, call.queue, expr, ctx, arena) ||
      DispatchQueueDelete(call.method, call.queue, expr, ctx, arena) ||
      ExecQueueOrdering(call, expr, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    AnnounceQueueChange(call.receiver, call.owner, ctx);
    return true;
  }
  return false;
}

bool TryExecQueueMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena) {
  QueueCall call = ResolveQueueCall(expr, ctx, arena);
  if (call.queue == nullptr) return false;
  if (DispatchQueuePush(call.method, call.queue, expr, ctx, arena) ||
      DispatchQueueDelete(call.method, call.queue, expr, ctx, arena)) {
    AnnounceQueueChange(call.receiver, call.owner, ctx);
    return true;
  }
  return false;
}

bool TryEvalQueueProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out) {
  auto* q = FindQueueOfName(var_name, ctx);
  if (!q) return false;

  return DispatchQueueEval(prop, q, arena, out);
}

static std::vector<size_t> QueueSortOrder(const QueueObject& q,
                                          bool ascending) {
  const auto& elems = q.elements;
  std::vector<size_t> order(elems.size());
  for (size_t i = 0; i < order.size(); ++i) order[i] = i;
  if (q.elem_width == 0 && !q.holds_class_handles && !q.elements_are_queues) {
    std::vector<std::string> text;
    text.reserve(elems.size());
    for (const auto& e : elems) text.push_back(Logic4VecToString(e));
    std::stable_sort(order.begin(), order.end(), [&](size_t a, size_t b) {
      return ascending ? text[a] < text[b] : text[a] > text[b];
    });
    return order;
  }
  std::stable_sort(order.begin(), order.end(), [&](size_t a, size_t b) {
    return ascending ? OrdersBefore(elems[a], elems[b], q.is_signed)
                     : OrdersBefore(elems[b], elems[a], q.is_signed);
  });
  return order;
}

static void SortQueueWithIds(QueueObject* q, bool ascending) {
  auto& elems = q->elements;
  auto& ids = q->element_ids;
  std::vector<size_t> order = QueueSortOrder(*q, ascending);
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

static bool OrderQueue(QueueObject* q, std::string_view prop, SimContext& ctx) {
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

bool TryExecQueuePropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena&) {
  auto* q = FindQueueOfName(var_name, ctx);
  if (!q) return false;
  if (prop == "delete") {
    q->elements.clear();
    q->element_ids.clear();
    ++q->generation;
    return true;
  }
  return OrderQueue(q, prop, ctx);
}

}  // namespace delta
