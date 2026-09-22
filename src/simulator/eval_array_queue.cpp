#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/evaluation.h"
#include "simulator/queue_bound.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
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
  auto val =
      SizedForQueueElement(*q, EvalExpr(expr->args[0], ctx, arena), arena);
  q->elements.push_back(val);
  q->element_ids.push_back(q->AllocateId());
  ++q->generation;
  EnforceQueueBound(q, "push_back", expr->range.start, ctx);
}

static void QueuePushFront(QueueObject* q, const Expr* expr, SimContext& ctx,
                           Arena& arena) {
  auto val =
      SizedForQueueElement(*q, EvalExpr(expr->args[0], ctx, arena), arena);
  q->elements.insert(q->elements.begin(), val);
  q->element_ids.insert(q->element_ids.begin(), q->AllocateId());
  EnforceQueueBound(q, "push_front", expr->range.start, ctx);
  ++q->generation;
}

static void QueueInsertAt(QueueObject* q, const Expr* expr, SimContext& ctx,
                          Arena& arena) {
  auto idx_val = EvalExpr(expr->args[0], ctx, arena);
  auto val =
      SizedForQueueElement(*q, EvalExpr(expr->args[1], ctx, arena), arena);
  if (!idx_val.IsKnown()) return;
  auto raw = static_cast<int64_t>(idx_val.ToUint64());
  if (idx_val.is_signed && raw < 0) return;
  auto idx = static_cast<size_t>(raw);
  if (idx <= q->elements.size()) {
    q->elements.insert(q->elements.begin() + static_cast<ptrdiff_t>(idx), val);
    q->element_ids.insert(q->element_ids.begin() + static_cast<ptrdiff_t>(idx),
                          q->AllocateId());
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

// The four ordering methods §7.12.2 defines over an array: sort and rsort put
// the elements in ascending and descending order, reverse and shuffle permute
// them. Syntax 7-5 of §7.12 makes the argument list of an array method call
// optional, so `q.sort` and `q.sort()` are the same call and both reach
// TryExecQueuePropertyStmt below. The four are named here rather than every
// method that dispatch declined being passed on, because that function also
// serves `delete`, which DispatchQueueDelete has already handled with its
// argument.
static bool IsQueueOrderingMethod(std::string_view method) {
  return method == "sort" || method == "rsort" || method == "reverse" ||
         method == "shuffle";
}

void NotifyOwningVar(SimContext& ctx, std::string_view var_name) {
  if (auto* v = ctx.FindVariable(var_name)) v->NotifyWatchers();
}

// The queue the call `receiver.method(...)` is on, with the receiver
// expression in `receiver`, the method in `method` and, for a property of an
// object, the object in `owner`; null for a call of another shape or on a
// receiver that names no queue. §7.10.2's methods are defined on the queue
// whatever names it: a declared queue by its bare name, and, §8.5 putting no
// restriction on a property's type, a property of an object -- the running
// method's own by its bare name (§8.11), any object's through a handle,
// `b.q.push_back(x)`, and a static one through `C::all.size()` (§8.9) --
// which FindQueueOfBase resolves. Before it, only the bare name of a declared
// queue was read here, so a queue property answered size 0 and kept nothing.
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
  call.queue = FindQueueOfBase(access->lhs, ctx, arena, &call.owner);
  return call;
}

// §7.12.2's ordering methods over the queue of `call`, which
// TryExecQueuePropertyStmt performs by the receiver's bare name and so for
// the queue a bare name resolves to: a declared one or the running method's
// property.
static bool ExecQueueOrdering(const QueueCall& call, SimContext& ctx,
                              Arena& arena) {
  return IsQueueOrderingMethod(call.method) &&
         call.receiver->kind == ExprKind::kIdentifier &&
         TryExecQueuePropertyStmt(call.receiver->text, call.method, ctx, arena);
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
      ExecQueueOrdering(call, ctx, arena)) {
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

// §7.10.2.1 writes `Q.size` without parentheses, and the name on the left of
// the dot is read as a call's receiver is: a declared queue, or the property
// of the running method's object (§8.11).
bool TryEvalQueueProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out) {
  auto* q = FindQueueOfName(var_name, ctx);
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
  auto* q = FindQueueOfName(var_name, ctx);
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
