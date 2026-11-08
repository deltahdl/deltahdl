#include <coroutine>
#include <cstddef>
#include <cstdint>
#include <iostream>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/awaiters.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/class_event_property.h"
#include "simulator/class_object.h"
#include "simulator/clocking.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/expr_walk.h"
#include "simulator/process.h"
#include "simulator/sequence_monitor.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"

namespace delta {
namespace {

void SubstituteSequenceEndpoints(std::unordered_set<std::string>& reads,
                                 SimContext& ctx) {
  std::unordered_set<std::string> seq_adds;
  std::unordered_set<std::string> seq_removes;
  for (const auto& name : reads) {
    if (ctx.FindSequenceDecl(name)) {
      std::string ep_name = "__seq_" + name;
      auto* ep_var = ctx.FindVariable(ep_name);
      if (!ep_var) {
        auto* stored = ctx.GetArena().Create<std::string>(ep_name);
        ep_var = ctx.CreateVariable(*stored, 1);
        ep_var->is_event = true;
      }
      seq_adds.insert(ep_name);
      seq_removes.insert(name);
      continue;
    }
    std::string ep_name = HierarchicalEndPoint(name, ctx);
    if (!ep_name.empty()) seq_adds.insert(ep_name);
  }
  for (const auto& r : seq_removes) reads.erase(r);
  for (auto& a : seq_adds) reads.insert(a);
}

const ClassTypeInfo* ScopedClassOf(const Expr* e, SimContext& ctx,
                                   std::string& scope) {
  if (e->lhs->kind == ExprKind::kIdentifier) {
    scope = std::string(e->lhs->text);
    return ctx.FindClassType(scope);
  }
  std::string_view member;
  const ClassTypeInfo* cls = PackageQualifiedClassOf(e, ctx, member);
  if (cls == nullptr) return nullptr;
  scope =
      std::string(e->lhs->lhs->text) + "::" + std::string(e->lhs->rhs->text);
  return cls;
}

void CollectStaticPropertyReads(const Expr* cond, SimContext& ctx,
                                std::unordered_set<std::string>& reads) {
  ForEachSubExpr(cond, [&](const Expr* e) {
    if (e->kind != ExprKind::kMemberAccess || !e->is_scope_resolution ||
        e->lhs == nullptr || e->rhs == nullptr ||
        e->rhs->kind != ExprKind::kIdentifier)
      return;
    std::string scope;
    const ClassTypeInfo* cls = ScopedClassOf(e, ctx, scope);
    if (cls == nullptr) return;
    std::string member(e->rhs->text);
    if (cls->StaticPropertyDeclarer(member) == nullptr) return;
    reads.insert(scope + "::" + member);
  });
}

void CollectPackageScopedReads(const Expr* cond, SimContext& ctx,
                               std::unordered_set<std::string>& reads) {
  ForEachSubExpr(cond, [&](const Expr* e) {
    if (e->kind != ExprKind::kMemberAccess || !e->is_scope_resolution ||
        e->lhs == nullptr || e->lhs->kind != ExprKind::kIdentifier ||
        e->rhs == nullptr || e->rhs->kind != ExprKind::kIdentifier)
      return;
    std::string key =
        std::string(e->lhs->text) + "." + std::string(e->rhs->text);
    if (ctx.FindVariable(key) != nullptr) reads.insert(std::move(key));
  });
}

void CollectMethodReceiverReads(const Expr* cond,
                                std::unordered_set<std::string>& reads) {
  ForEachSubExpr(cond, [&](const Expr* e) {
    if (e->kind != ExprKind::kCall || e->lhs == nullptr ||
        e->lhs->kind != ExprKind::kMemberAccess || e->lhs->is_scope_resolution)
      return;
    CollectExprReads(e->lhs->lhs, reads);
  });
}

struct WaitOrderStepAwaiter {
  SimContext& ctx;
  const std::vector<Variable*>& events;
  size_t triggered = 0;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    auto done = std::make_shared<bool>(false);
    auto* out = &triggered;
    auto* ctx_ptr = &ctx;
    Process* proc = ctx.CurrentProcess();
    for (size_t k = 0; k < events.size(); ++k) {
      if (events[k] == nullptr) continue;
      events[k]->AddWatcher([h, k, out, done, ctx_ptr, proc]() mutable {
        if (*done) return true;
        *done = true;
        *out = k;
        EventAwaiter::ResumeMaybeReactive(h, proc, *ctx_ptr);
        return true;
      });
    }
  }

  size_t await_resume() const noexcept { return triggered; }
};

std::vector<Variable*> WaitOrderEvents(const std::vector<Expr*>& operands,
                                       SimContext& ctx) {
  std::vector<Variable*> events;
  events.reserve(operands.size());
  for (const Expr* operand : operands) {
    std::string_view name =
        operand->kind == ExprKind::kIdentifier ? operand->text : "";
    events.push_back(TriggerTargetEvent(operand, name, ctx));
  }
  return events;
}

}  // namespace

void CollectExprAndStaticReads(const Expr* expr, SimContext& ctx,
                               std::unordered_set<std::string>& reads) {
  CollectExprReads(expr, reads);
  CollectStaticPropertyReads(expr, ctx, reads);
  CollectPackageScopedReads(expr, ctx, reads);
}

static void CollectClockvarReads(const Expr* cond, SimContext& ctx,
                                 std::unordered_set<std::string>& reads) {
  auto* mgr = ctx.GetClockingManager();
  if (mgr == nullptr) return;
  ForEachSubExpr(cond, [&](const Expr* e) {
    if (e->kind != ExprKind::kMemberAccess || e->lhs == nullptr) return;
    const ClockingBlock* block = ResolveClockingBlockOf(e->lhs, ctx);
    if (block == nullptr) return;
    std::string_view field =
        e->rhs != nullptr && e->rhs->kind == ExprKind::kIdentifier
            ? e->rhs->text
            : e->text;
    if (mgr->FindBlockSignal(*block, field) == nullptr) return;
    reads.insert(ClockingManager::SampleVariableName(block->name, field));
  });
}

ExecTask ExecWait(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(ctx.StmtFrameName(stmt));
  std::unordered_set<std::string> reads;
  CollectExprReads(stmt->condition, reads);
  CollectClockvarReads(stmt->condition, ctx, reads);
  CollectMethodReceiverReads(stmt->condition, reads);
  CollectStaticPropertyReads(stmt->condition, ctx, reads);
  CollectPackageScopedReads(stmt->condition, ctx, reads);

  SubstituteSequenceEndpoints(reads, ctx);
  std::vector<std::string_view> read_vars(reads.begin(), reads.end());
  auto finished = std::make_shared<bool>(false);
  bool suspended = false;
  while (!ctx.StopRequested()) {
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (cond.IsTruthy()) break;
    suspended = true;
    co_await AnyChangeAwaiter{ctx, read_vars, finished};
  }
  *finished = true;
  if (suspended) {
    ctx.FlushPendingViolations();
    ctx.FlushPendingDeferredReports();
  }
  if (stmt->body) {
    auto r = co_await ExecStmt(stmt->body, ctx, arena);
    if (labeled) ctx.PopStaticScope(ctx.StmtFrameName(stmt));
    co_return r;
  }
  if (labeled) ctx.PopStaticScope(ctx.StmtFrameName(stmt));
  co_return StmtResult::kDone;
}

ExecTask ExecWaitOrder(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto& events = stmt->wait_order_events;
  if (events.empty()) {
    if (stmt->then_branch) {
      co_return co_await ExecStmt(stmt->then_branch, ctx, arena);
    }
    co_return StmtResult::kDone;
  }

  bool failed = false;
  std::vector<Variable*> vars = WaitOrderEvents(events, ctx);
  uint64_t now = ctx.CurrentTime().ticks;

  bool suspended = false;
  for (size_t i = 0; i < vars.size() && !failed; ++i) {
    if (i == 0 && vars[0] != nullptr && vars[0]->triggered_ticks == now) {
      continue;
    }
    std::vector<Variable*> remaining(
        vars.begin() + static_cast<std::ptrdiff_t>(i), vars.end());
    size_t triggered = co_await WaitOrderStepAwaiter{ctx, remaining, 0};
    suspended = true;
    if (triggered != 0) failed = true;
  }
  if (suspended) {
    ctx.FlushPendingViolations();
    ctx.FlushPendingDeferredReports();
  }

  if (failed) {
    if (stmt->else_branch) {
      co_return co_await ExecStmt(stmt->else_branch, ctx, arena);
    }

    EmitSeverityHeader(ctx, "ERROR", "wait_order events triggered out of order",
                       std::cerr);
    co_return StmtResult::kDone;
  }

  if (stmt->then_branch) {
    co_return co_await ExecStmt(stmt->then_branch, ctx, arena);
  }
  co_return StmtResult::kDone;
}

ExecTask ExecCycleDelay(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  uint32_t cycles = 0;
  if (stmt->cycle_delay) {
    auto val = EvalExpr(stmt->cycle_delay, ctx, arena);
    cycles = static_cast<uint32_t>(val.ToUint64());
  }
  co_await CycleDelayAwaiter{ctx, cycles};
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

uint64_t DelayTicksFromValue(const Logic4Vec& val) {
  if (!val.IsKnown()) return 0;
  uint64_t raw = val.ToUint64();
  if (val.is_signed && val.width > 0 && val.width < 64) {
    int64_t signed_val = SignExtend(raw, val.width);
    if (signed_val < 0) return static_cast<uint64_t>(signed_val);
  }
  return raw;
}

uint64_t DelayValueToTicks(const Logic4Vec& val, const SimContext& ctx) {
  return DelayValueToTicksIn(val, ActiveInstanceTimeScale(ctx),
                             ctx.GlobalPrecision());
}

uint64_t DelayValueToTicksIn(const Logic4Vec& val, const TimeScale& scale,
                             TimeUnit precision) {
  if (val.is_real) {
    double d = RealVecToDouble(val);
    if (d < 0.0) return 0;
    return RealDelayToTicks(d, scale, precision);
  }
  return DelayToTicks(DelayTicksFromValue(val), scale, precision);
}

static bool IsOneStepDelay(const Expr* delay) {
  return delay->kind == ExprKind::kIntegerLiteral && delay->text == "1step";
}

uint64_t DelayExprToTicks(const Expr* delay, SimContext& ctx, Arena& arena) {
  if (IsOneStepDelay(delay)) return 1;
  return DelayValueToTicks(EvalExpr(delay, ctx, arena), ctx);
}

uint64_t DelayExprToTicksIn(const Expr* delay, const TimeScale& scale,
                            SimContext& ctx, Arena& arena) {
  if (IsOneStepDelay(delay)) return 1;
  return DelayValueToTicksIn(EvalExpr(delay, ctx, arena), scale,
                             ctx.GlobalPrecision());
}

ExecTask ExecDelay(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  uint64_t ticks = 0;
  if (stmt->delay) {
    ticks = DelayExprToTicks(stmt->delay, ctx, arena);
  }
  co_await DelayAwaiter{ctx, ticks};
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

static std::string_view NamedEventKey(const Stmt* stmt, SimContext& ctx) {
  if (stmt->events.size() != 1) return {};
  const auto& ev = stmt->events[0];
  if (ev.edge != Edge::kNone) return {};
  if (ev.iff_condition) return {};
  std::string_view key = ScopedOrBareTargetKey(ev.signal, ctx.GetArena());
  if (key.empty()) return {};
  auto* var = ctx.FindVariable(key);
  return var && var->is_event ? key : std::string_view{};
}

static bool HasSequenceEvent(const Stmt* stmt) {
  for (const auto& ev : stmt->events) {
    if (ev.is_sequence_event) return true;
  }
  return false;
}

static Variable* ClassEventOfControl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  if (stmt->events.size() != 1) return nullptr;
  const auto& ev = stmt->events[0];
  if (ev.edge != Edge::kNone || ev.iff_condition) return nullptr;
  if (Variable* var = ClassEventVariable(ev.signal, ctx, arena)) return var;
  return EventArrayElement(ev.signal, ctx, arena);
}

ExecTask ExecEventControl(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->events.empty()) {
    std::string_view named_event = NamedEventKey(stmt, ctx);
    Variable* class_event =
        named_event.empty() ? ClassEventOfControl(stmt, ctx, arena) : nullptr;
    if (!HasSequenceEvent(stmt) &&
        (!named_event.empty() || class_event != nullptr)) {
      co_await NamedEventAwaiter{ctx, named_event, class_event};
    } else {
      co_await EventAwaiter{ctx, stmt->events, arena};
    }
    ctx.FlushPendingViolations();
    ctx.FlushPendingDeferredReports();
  } else if (stmt->is_star_event && stmt->body) {
    std::vector<EventExpr> implicit_events =
        InferSensitivity(stmt->body, arena, nullptr, false);
    if (!implicit_events.empty()) {
      co_await EventAwaiter{ctx, implicit_events, arena};
      ctx.FlushPendingViolations();
      ctx.FlushPendingDeferredReports();
    }
  }
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

}  // namespace delta
