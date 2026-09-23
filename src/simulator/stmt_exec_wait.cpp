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
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/expr_walk.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"

namespace delta {
namespace {

// Rewrites any sequence name in the wait condition's read set to its synthetic
// endpoint event variable (creating that event variable on demand), so the wait
// suspends on the sequence's completion event rather than on the name itself.
void SubstituteSequenceEndpoints(std::unordered_set<std::string>& reads,
                                 SimContext& ctx) {
  std::unordered_set<std::string> seq_adds;
  std::unordered_set<std::string> seq_removes;
  for (const auto& name : reads) {
    if (ctx.FindSequenceDecl(name)) {
      std::string ep_name = "__seq_" + name;
      auto* ep_var = ctx.FindVariable(ep_name);
      if (!ep_var) {
        // variables_ keys by string_view, so intern the name in the arena;
        // a local std::string key would dangle once this function returns.
        auto* stored = ctx.GetArena().Create<std::string>(ep_name);
        ep_var = ctx.CreateVariable(*stored, 1);
        ep_var->is_event = true;
      }
      seq_adds.insert(ep_name);
      seq_removes.insert(name);
    }
  }
  for (const auto& r : seq_removes) reads.erase(r);
  for (auto& a : seq_adds) reads.insert(a);
}

// §8.9 with §26.3: the class the scope resolution `e` names a member of --
// `C` by one identifier, or `p::C`, the key the lowerer binds a package's
// class under, which PackageQualifiedClassOf (eval_static_method.cpp) answers
// for the doubly-qualified `p::C::all` -- and in `scope` the name the class
// was written by. Null for a left side that is no class.
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

// §9.4.3 with §8.9: the static properties the wait condition reads through
// the class scope operator, each added to `reads` as `C::n`, which is the
// name AnyChangeAwaiter::AttachStaticPropertyWatcher arms on the class by.
// CollectExprReads descends a scope resolution into its two identifiers, `C`
// and `n`, and neither names the class's own storage: a class is not a
// variable, and a wait on `C::n == 2` therefore armed nothing and waited for
// ever. The two are left in the set, harmless where they name nothing and
// dropped by the awaiter if they do not. §26.3: a package's class is named
// `p::C`, so `p::C::all` is added as `p::C::all`, which the awaiter splits at
// its last scope operator; read for a class named by one identifier alone,
// `wait (p::C::all.size() != 0)` collected `p`, `C` and `all`, none a
// variable, armed nothing and waited for ever. §8.13 (printed pages
// 189-190): a derived class inherits its base's static properties, so `D::n`
// and `D::all` name C's own storage where D extends C, and are added under
// the written `D` for the awaiter to resolve to the declaring class
// (ClassTypeInfo::StaticPropertyDeclarer); asked of D's own
// static_properties, which hold D's declarations alone, neither was added
// and each waited for ever.
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

// §15.5.3 (printed page 378) with §26.3 (printed 808): the wait condition
// names a hierarchical_event_identifier's triggered state, and a package's
// event is named through the package scope resolution operator,
// `wait (p1::e.triggered)`, whose storage stands under the "p1.e" key
// CreatePackageDataVariables (lowerer_package_data.cpp) creates it under.
// CollectExprReads descends the scope resolution into `p1` and `e`, neither
// of which names that storage, so nothing was armed on the event and the
// process waited for ever; each scoped name whose key holds a variable is
// added to `reads` under that key, which AnyChangeAwaiter arms on and the
// trigger's `-> p1::e` wakes (ExecEventTriggerImpl in stmt_exec.cpp). A
// scoped name of any other package item, a variable or a parameter, is
// added the same way, its key holding its storage too.
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

// §9.4.3 with §7.10.2 and §7.5.2: the condition may read a queue or a dynamic
// array through a method call, `wait (q.size() != 0)`, and the methods that
// answer about the array are defined on the object the receiver names, as are
// the ones that change it. CollectExprReads gives a call its arguments alone,
// a callee being no variable, so a call on a receiver contributed nothing to
// `reads`: the set was empty, and ExecWait returned at once with the condition
// still false -- `wait (q.size() != 0)` on an empty queue popped 0 at time 0
// where the push at time 10 should have released it, and a class task's
// `wait (m_queue.size() != 0)` called from a forever loop spun at time 0. The
// receiver's own reads are what the call adds: a declared queue's or dynamic
// array's name, which every mutating method announces through NotifyOwningVar
// (eval_array_queue.cpp) while the variable's value stands still, and which
// AnyChangeAwaiter therefore wakes on without comparing; a property's bare
// name inside a method, which the awaiter's own-property arm arms on the
// running method's object; and the handle a property is reached through,
// `h.m_queue.size()`, which AnnounceQueueChange (eval_array_class_queue.cpp)
// reaches through SimContext::NotifyClassHandleWatchers. A parenthesis-less
// `q.size` is a member access, whose two sides CollectExprReads already
// descends, which is why that spelling was released and the call was not.
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
  const std::vector<std::string_view>& event_names;
  std::string_view triggered_name;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    auto done = std::make_shared<bool>(false);
    auto* out = &triggered_name;

    for (auto name : event_names) {
      auto* var = ctx.FindVariable(name);
      if (!var) continue;
      var->AddWatcher([h, name, out, done]() mutable {
        if (*done) return true;
        *done = true;
        *out = name;
        h.resume();
        return true;
      });
    }
  }

  std::string_view await_resume() const noexcept { return triggered_name; }
};

// Collects the names of the wait_order events from index `start` onward, the
// set the next step must wait on while honoring the required ordering.
std::vector<std::string_view> RemainingWaitOrderNames(
    const std::vector<Expr*>& events, size_t start) {
  std::vector<std::string_view> remaining;
  for (size_t j = start; j < events.size(); ++j) {
    remaining.push_back(events[j]->text);
  }
  return remaining;
}

}  // namespace

ExecTask ExecWait(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  std::unordered_set<std::string> reads;
  CollectExprReads(stmt->condition, reads);
  CollectMethodReceiverReads(stmt->condition, reads);
  CollectStaticPropertyReads(stmt->condition, ctx, reads);
  CollectPackageScopedReads(stmt->condition, ctx, reads);

  SubstituteSequenceEndpoints(reads, ctx);
  std::vector<std::string_view> read_vars(reads.begin(), reads.end());
  // Shared with every watcher armed below: set true once the condition holds
  // and this coroutine resumes for good, so a watcher still stranded on a
  // sibling signal removes itself instead of resuming the (freed) frame.
  auto finished = std::make_shared<bool>(false);
  bool suspended = false;
  while (!ctx.StopRequested()) {
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (cond.IsTruthy()) break;
    if (read_vars.empty()) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return StmtResult::kDone;
    }
    suspended = true;
    co_await AnyChangeAwaiter{ctx, read_vars, finished};
  }
  *finished = true;
  // §12.4.2.1: resuming after suspending on a wait statement is a violation
  // report flush point; drop any reports pending from before the wait.
  // §16.4.2: the same resume is a deferred assertion flush point.
  if (suspended) {
    ctx.FlushPendingViolations();
    ctx.FlushPendingDeferredReports();
  }
  if (stmt->body) {
    auto r = co_await ExecStmt(stmt->body, ctx, arena);
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return r;
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
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

  for (size_t i = 0; i < events.size() && !failed; ++i) {
    auto expected_name = events[i]->text;

    if (i == 0 && ctx.IsEventTriggered(expected_name)) {
      continue;
    }

    std::vector<std::string_view> remaining =
        RemainingWaitOrderNames(events, i);

    auto triggered = co_await WaitOrderStepAwaiter{ctx, remaining, {}};

    if (triggered != expected_name) {
      failed = true;
    }
  }

  if (failed) {
    if (stmt->else_branch) {
      co_return co_await ExecStmt(stmt->else_branch, ctx, arena);
    }

    // §15.5.4: when no else (fail) clause is supplied, a failed sequence
    // raises a default run-time error by calling $error (see §20.10), which
    // records ERROR severity and lets the run continue.
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
  if (cycles > 0) {
    co_await CycleDelayAwaiter{ctx, cycles};
  }
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
  const TimeScale& scale = ctx.CurrentTimeScale();
  TimeUnit precision = ctx.GlobalPrecision();
  if (val.is_real) {
    // §3.14.1: a real delay is rounded to the nearest multiple of the design
    // element's time precision before it is used. The value carries IEEE-754
    // bits in its low word; recover the number and let RealDelayToTicks apply
    // the precision-step rounding and scale the result to global-precision
    // ticks. A negative delay has no meaning here, so it collapses to no wait.
    double d = RealVecToDouble(val);
    if (d < 0.0) return 0;
    return RealDelayToTicks(d, scale, precision);
  }
  // An integer delay has no fractional part to round, but is still scaled from
  // the issuing element's time unit to the global tick base.
  return DelayToTicks(DelayTicksFromValue(val), scale, precision);
}

ExecTask ExecDelay(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  uint64_t ticks = 0;
  if (stmt->delay) {
    ticks = DelayValueToTicks(EvalExpr(stmt->delay, ctx, arena), ctx);
  }
  co_await DelayAwaiter{ctx, ticks};
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

// §15.5.2 (printed page 378): the key of the named event an event control's
// one operand names, empty where the control names anything else. §26.3
// (printed 808): the operand is a hierarchical_event_identifier, which a
// package's event is written as through the package scope resolution
// operator, `@(p1::e)`, so the operand is read as ScopedOrBareTargetKey
// (eval_semaphore.cpp) reads a semaphore's `p1::s = new` target -- an
// identifier's own text, or the "p1.e" key a scoped name's storage stands
// under -- and the awaiter arms on that key. Read as an identifier alone,
// the scoped operand fell to EventAwaiter, which resolved no variable for it
// and never resumed the process.
static std::string_view NamedEventKey(const Stmt* stmt, SimContext& ctx) {
  if (stmt->events.size() != 1) return {};
  const auto& ev = stmt->events[0];
  if (ev.edge != Edge::kNone) return {};
  // §9.4.2.3: a guarded operand goes to EventAwaiter, which evaluates the
  // condition before resuming. NamedEventAwaiter resumes on the trigger alone,
  // so sending `@(e iff en)` there would fire the process however `en` read.
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

// §6.17 with §9.4.2: the event a single event control with no edge and no
// guard waits on where its operand names a class's event property, `@(h.ev)`
// or `@(ev)` in a method (ClassEventVariable); null otherwise, and where the
// operand is a declared event NamedEventKey finds by name.
static Variable* ClassEventOfControl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  if (stmt->events.size() != 1) return nullptr;
  const auto& ev = stmt->events[0];
  if (ev.edge != Edge::kNone || ev.iff_condition) return nullptr;
  return ClassEventVariable(ev.signal, ctx, arena);
}

ExecTask ExecEventControl(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->events.empty()) {
    std::string_view named_event = NamedEventKey(stmt, ctx);
    Variable* class_event =
        named_event.empty() ? ClassEventOfControl(stmt, ctx, arena) : nullptr;
    if (HasSequenceEvent(stmt)) {
      co_await SequenceEventAwaiter{ctx, stmt->events};
    } else if (!named_event.empty() || class_event != nullptr) {
      co_await NamedEventAwaiter{ctx, named_event, class_event};
    } else {
      co_await EventAwaiter{ctx, stmt->events, arena};
    }
    // §12.4.2.1: a process that suspended on an event control reaches a
    // violation report flush point when it resumes; any unique/priority
    // reports accumulated before the suspension are discarded.
    ctx.FlushPendingViolations();
    // §16.4.2: that resume is equally a deferred assertion flush point, so
    // deferred reports pending from before the suspend are cleared as well.
    ctx.FlushPendingDeferredReports();
  } else if (stmt->is_star_event && stmt->body) {
    // §9.4.2.2: a procedural @* (or @(*)) carries no explicit operand list; it
    // suspends until any net or variable read by its controlled statement
    // changes. Derive that implicit event list from the statement's reads --
    // the same read-collection rule the elaborator applies to `always @*` --
    // and wait on it as though it had been written out as @(a or b or ...).
    // The vector must outlive the suspension, so it lives in this coroutine
    // frame. `exclude_written` is false because @* (unlike always_comb) still
    // lists a signal that is both read and written.
    std::vector<EventExpr> implicit_events = InferSensitivity(
        stmt->body, arena, /*funcs=*/nullptr, /*exclude_written=*/false);
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
