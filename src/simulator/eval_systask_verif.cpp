#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <iterator>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/assertion_control_task.h"
#include "parser/ast_expr.h"
#include "simulator/assert_control_log.h"
#include "simulator/assertion_api.h"
#include "simulator/assertion_attempt_events.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/expr_walk.h"
#include "simulator/scheduler.h"
#include "simulator/scope_hier_name.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/stmt_exec_assertion_internal.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/sva_engine_queues.h"
#include "simulator/sva_engine_sampling.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"

namespace delta {

// §20.15.6 Table 20-11 status code values returned through the trailing
// `status` output argument of every stochastic-analysis queue task and
// function. Value 7, a queue that could not be created for want of memory, is
// defined by the table but has no deterministic trigger in the model, so
// nothing emits it.
enum QueueStatus : std::uint8_t {
  kQOk = 0,                 // OK
  kQFullCannotAdd = 1,      // queue full, cannot add
  kQUndefinedId = 2,        // undefined q_id
  kQEmptyCannotRemove = 3,  // queue empty, cannot remove
  kQUnsupportedType = 4,    // unsupported queue type, cannot create
  kQNonPositiveLength = 5,  // specified length <= 0, cannot create
  kQDuplicateId = 6,        // duplicate q_id, cannot create
};

// Local aliases matching the concrete types of expr->args and
// SimContext::StochasticQueues(), shared by the per-task helpers below.
using QueueArgList = std::vector<Expr*>;
using StochasticQueueMap = std::unordered_map<uint64_t, StochasticQueue>;

// Read an argument as a signed value, sign-extending from its own width so a
// negative max_length is recognized as such (Table 20-11 status 5 keys on
// length <= 0).
static int64_t QueueSignedArg(const Logic4Vec& v) {
  uint64_t raw = v.ToUint64();
  uint32_t w = v.width;
  if (w == 0 || w >= 64) return static_cast<int64_t>(raw);
  uint64_t sign_bit = 1ull << (w - 1);
  if (raw & sign_bit) raw |= ~((1ull << w) - 1);
  return static_cast<int64_t>(raw);
}

// §20.15.6: deliver the resolved status code into the queue task's `status`
// output argument, which every queue task and function returns.
static void WriteQueueStatus(const Expr* status_arg, uint64_t status,
                             SimContext& ctx, Arena& arena) {
  if (!status_arg || status_arg->kind != ExprKind::kIdentifier) return;
  auto* var = ctx.FindVariable(status_arg->text);
  // §9.4.2: an implicit event with no edge is detected on any change in the
  // expression's value, and the clause names no writer whose change is
  // exempt -- a queue task's output argument is a user variable, and
  // Variable::NotifyWatchers is the only route by which a process parked on it
  // resumes.
  if (var) {
    var->value = MakeLogic4VecVal(arena, var->value.width, status);
    var->NotifyWatchers();
  }
}

// §20.15.3: write an integer value back through one of $q_remove's output
// arguments (job_id, inform_id), keeping the destination variable's own width.
static void WriteQueueOutput(const Expr* out_arg, uint64_t value,
                             SimContext& ctx, Arena& arena) {
  if (!out_arg || out_arg->kind != ExprKind::kIdentifier) return;
  auto* var = ctx.FindVariable(out_arg->text);
  if (var) {
    var->value = MakeLogic4VecVal(arena, var->value.width, value);
    var->NotifyWatchers();
  }
}

// §20.15.1 $q_initialize(q_id, q_type, max_length, status): create a queue of
// the named type and capacity, reporting the Table 20-11 outcome.
static Logic4Vec EvalQueueInitialize(const QueueArgList& args,
                                     StochasticQueueMap& queues,
                                     SimContext& ctx, Arena& arena) {
  if (args.size() < 4) return MakeLogic4VecVal(arena, 32, 0);
  uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
  int64_t q_type = QueueSignedArg(EvalExpr(args[1], ctx, arena));
  int64_t max_length = QueueSignedArg(EvalExpr(args[2], ctx, arena));
  uint64_t status = 0;
  if (q_type != 1 && q_type != 2) {
    status = kQUnsupportedType;
  } else if (max_length <= 0) {
    status = kQNonPositiveLength;
  } else if (queues.count(q_id)) {
    status = kQDuplicateId;
  } else {
    queues[q_id] = StochasticQueue{q_type, max_length, 0};
    status = kQOk;
  }
  WriteQueueStatus(args[3], status, ctx, arena);
  return MakeLogic4VecVal(arena, 32, status);
}

// §20.15.2 $q_add(q_id, job_id, inform_id, status): append an entry to the
// queue named by q_id, stamping it for the §20.15.5 statistics.
static Logic4Vec EvalQueueAdd(const QueueArgList& args,
                              StochasticQueueMap& queues, SimContext& ctx,
                              Arena& arena) {
  if (args.size() < 4) return MakeLogic4VecVal(arena, 32, 0);
  uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
  auto it = queues.find(q_id);
  uint64_t status = 0;
  if (it == queues.end()) {
    status = kQUndefinedId;
  } else if (static_cast<int64_t>(it->second.count) >= it->second.max_length) {
    status = kQFullCannotAdd;
  } else {
    // Retain the entry's identifiers so §20.15.3 $q_remove can return them;
    // the inform_id holds whatever value $q_add was handed (its meaning is
    // user-defined).
    uint64_t job_id = EvalExpr(args[1], ctx, arena).ToUint64();
    uint64_t inform_id = EvalExpr(args[2], ctx, arena).ToUint64();
    // §20.15.5: stamp the arrival time and fold it into the queue's activity
    // statistics so $q_exam can report mean interarrival time, peak occupancy
    // and wait times.
    uint64_t now = ctx.CurrentTime().ticks;
    auto& q = it->second;
    q.entries.push_back(StochasticQueueEntry{job_id, inform_id, now});
    if (q.arrivals == 0) q.first_arrival_tick = now;
    q.last_arrival_tick = now;
    ++q.arrivals;
    ++q.count;
    if (q.count > q.max_count) q.max_count = q.count;
    status = kQOk;
  }
  WriteQueueStatus(args[3], status, ctx, arena);
  return MakeLogic4VecVal(arena, 32, status);
}

// §20.15.3 $q_remove(q_id, job_id, inform_id, status): take an entry off the
// queue selected by q_id (an integer input) and report the removed entry's
// identifiers through the job_id and inform_id outputs.
static Logic4Vec EvalQueueRemove(const QueueArgList& args,
                                 StochasticQueueMap& queues, SimContext& ctx,
                                 Arena& arena) {
  if (args.size() < 4) return MakeLogic4VecVal(arena, 32, 0);
  uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
  auto it = queues.find(q_id);
  uint64_t status = 0;
  if (it == queues.end()) {
    status = kQUndefinedId;
  } else if (it->second.count == 0) {
    status = kQEmptyCannotRemove;
  } else {
    // Choose the entry per the discipline fixed at $q_initialize: q_type 2
    // (LIFO) returns the most recently added entry, otherwise q_type 1
    // (FIFO) returns the oldest. $q_add always appends to the back.
    auto& q = it->second;
    StochasticQueueEntry entry;
    if (q.q_type == 2) {
      entry = q.entries.back();
      q.entries.pop_back();
    } else {
      entry = q.entries.front();
      q.entries.pop_front();
    }
    --q.count;
    // §20.15.5: a removed entry's residence time completes a wait sample,
    // feeding the shortest-ever and average wait-time statistics reported by
    // $q_exam.
    uint64_t now = ctx.CurrentTime().ticks;
    uint64_t wait = now >= entry.arrival_tick ? now - entry.arrival_tick : 0;
    if (q.departures == 0 || wait < q.shortest_wait) q.shortest_wait = wait;
    q.total_wait += wait;
    ++q.departures;
    WriteQueueOutput(args[1], entry.job_id, ctx, arena);
    WriteQueueOutput(args[2], entry.inform_id, ctx, arena);
    status = kQOk;
  }
  WriteQueueStatus(args[3], status, ctx, arena);
  return MakeLogic4VecVal(arena, 32, status);
}

// §20.15.4: $q_full checks whether the queue named by q_id has room for
// another entry, returning 1 when it is full and 0 when it is not. A queue is
// full once its occupancy reaches the capacity fixed at $q_initialize. The
// trailing status reports the operation outcome (§20.15.6); the only error
// condition that applies is an undefined q_id.
static Logic4Vec EvalQueueFull(const QueueArgList& args,
                               StochasticQueueMap& queues, SimContext& ctx,
                               Arena& arena) {
  if (args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
  auto it = queues.find(q_id);
  WriteQueueStatus(args[1], it == queues.end() ? kQUndefinedId : kQOk, ctx,
                   arena);
  uint64_t full =
      (it != queues.end() &&
       static_cast<int64_t>(it->second.count) >= it->second.max_length)
          ? 1u
          : 0u;
  return MakeLogic4VecVal(arena, 32, full);
}

// §20.15.5: compute the Table 20-10 statistic selected by `code` for queue `q`
// at the current time `now`. Unknown codes report 0, matching $q_exam's
// default.
static uint64_t QueueExamStatistic(const StochasticQueue& q, int64_t code,
                                   uint64_t now) {
  switch (code) {
    case 1:  // Current queue length.
      return q.count;
    case 2:  // Mean interarrival time: total span between the first and last
             // arrival divided by the number of gaps between arrivals.
      return q.arrivals > 1 ? (q.last_arrival_tick - q.first_arrival_tick) /
                                  (q.arrivals - 1)
                            : 0;
    case 3:  // Maximum queue length ever reached.
      return q.max_count;
    case 4:  // Shortest wait time ever, across removed entries.
      return q.departures ? q.shortest_wait : 0;
    case 5:  // Longest wait among entries still queued: the oldest entry is
             // at the front, as $q_add appends in arrival order.
      return q.entries.empty() ? 0
                               : (now >= q.entries.front().arrival_tick
                                      ? now - q.entries.front().arrival_tick
                                      : 0);
    case 6:  // Average wait time over removed entries.
      return q.departures ? q.total_wait / q.departures : 0;
    default:
      return 0;
  }
}

// §20.15.5 $q_exam(q_id, q_stat_code, q_stat_value, status): report a
// statistic about activity on the queue named by q_id. The q_stat_code selects
// which statistic is delivered through the q_stat_value output, per Table
// 20-10. An undefined q_id is the only applicable error (§20.15.6).
static Logic4Vec EvalQueueExam(const QueueArgList& args,
                               StochasticQueueMap& queues, SimContext& ctx,
                               Arena& arena) {
  if (args.size() < 4) return MakeLogic4VecVal(arena, 32, 0);
  uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
  auto it = queues.find(q_id);
  if (it == queues.end()) {
    WriteQueueStatus(args[3], kQUndefinedId, ctx, arena);
    return MakeLogic4VecVal(arena, 32, kQUndefinedId);
  }
  const auto& q = it->second;
  int64_t code = QueueSignedArg(EvalExpr(args[1], ctx, arena));
  uint64_t now = ctx.CurrentTime().ticks;
  uint64_t value = QueueExamStatistic(q, code, now);
  WriteQueueOutput(args[2], value, ctx, arena);
  WriteQueueStatus(args[3], kQOk, ctx, arena);
  return MakeLogic4VecVal(arena, 32, kQOk);
}

// §20.15.6: resolve and report the Table 20-11 status code for each
// stochastic-analysis queue task/function. The queue type/capacity validated
// at $q_initialize and the occupancy tracked across $q_add/$q_remove supply
// the error conditions. $q_remove additionally returns its removed entry's
// job_id/inform_id outputs (§20.15.3), $q_full its fullness result (§20.15.4),
// and $q_exam its requested statistic (§20.15.5) through the q_stat_value
// output.
static Logic4Vec EvalStochasticQueue(const Expr* expr, SimContext& ctx,
                                     Arena& arena, std::string_view name) {
  auto& queues = ctx.StochasticQueues();
  const auto& args = expr->args;

  if (name == "$q_initialize")
    return EvalQueueInitialize(args, queues, ctx, arena);
  if (name == "$q_add") return EvalQueueAdd(args, queues, ctx, arena);
  if (name == "$q_remove") return EvalQueueRemove(args, queues, ctx, arena);
  if (name == "$q_full") return EvalQueueFull(args, queues, ctx, arena);
  if (name == "$q_exam") return EvalQueueExam(args, queues, ctx, arena);

  return MakeLogic4VecVal(arena, 32, 0);
}

// §20.11: the full hierarchical names the scope list item `item` may stand
// for where it is written in the scope `caller`: the name as written, and the
// name as read from `caller` and from each scope above it, as §23.8 resolves a
// name upward.
std::vector<std::string> ScopeItemNames(const Expr* item,
                                        std::string_view caller) {
  std::string written = item->kind == ExprKind::kIdentifier
                            ? std::string(item->text)
                            : FlattenHierPath(item);
  std::vector<std::string> names{written};
  for (std::string_view scope = caller; !scope.empty();) {
    names.push_back(std::string(scope) + "." + written);
    size_t dot = scope.rfind('.');
    scope = dot == std::string_view::npos ? std::string_view{}
                                          : scope.substr(0, dot);
  }
  return names;
}

// Table 20-8: the callbacks an assertion control task raises, by its
// control_type: the assertion system callback (§39.4.1) of a call naming no
// scope or assertion, and the assertion callbacks (§39.4.2) a call naming some
// raises on each assertion it selects, Kill raising a reset before its disable.
// The row of a control_type Table 20-5 does not list raises none.
namespace {
struct ControlCallbacks {
  int system;
  int first;
  int second;
};
constexpr ControlCallbacks kControlCallbacks[] = {
    {0, 0, 0},
    {cbAssertionSysLock, cbAssertionLock, 0},
    {cbAssertionSysUnlock, cbAssertionUnlock, 0},
    {cbAssertionSysOn, cbAssertionEnable, 0},
    {cbAssertionSysOff, cbAssertionDisable, 0},
    {cbAssertionSysKill, cbAssertionReset, cbAssertionDisable},
    {cbAssertionSysEnablePassAction, cbAssertionEnablePassAction, 0},
    {cbAssertionSysDisablePassAction, cbAssertionDisablePassAction, 0},
    {cbAssertionSysEnableFailAction, cbAssertionEnableFailAction, 0},
    {cbAssertionSysDisableFailAction, cbAssertionDisableFailAction, 0},
    {cbAssertionSysEnableNonvacuousAction, cbAssertionEnableNonvacuousAction,
     0},
    {cbAssertionSysDisableVacuousAction, cbAssertionDisableVacuousAction, 0}};
}  // namespace

// Table 20-8: raise the callbacks of `call`. The assertions it may select are
// those an application placed callbacks on, the only ones a callback reaches.
static void RaiseControlCallbacks(const AssertControlCall& call,
                                  SimContext& ctx) {
  if (call.control_type >= std::size(kControlCallbacks)) return;
  const ControlCallbacks& raised = kControlCallbacks[call.control_type];
  if (call.scopes.empty()) {
    GetGlobalVpiContext().DispatchCallbacks(raised.system);
    return;
  }
  AssertionApi& api = GetGlobalAssertionApi();
  for (const auto& [name, target] : api.ControlTargets()) {
    if (!CallSelects(call, {target.type_bit, target.directive_bit, target.scope,
                            target.full_name})) {
      continue;
    }
    for (int reason : {raised.first, raised.second}) {
      if (reason != 0) RaiseAssertionControlCallback(name, reason, ctx);
    }
  }
}

// §20.11: an assertion control system task, recorded in the terms of the
// $assertcontrol call it is or expands to (Syntax 20-12): control_type, then
// assertion_type and directive_type, defaulting to 255 and 7, then levels,
// defaulting to 0, and the list_of_scopes_or_assertions, which a convenience
// task begins its own arguments with. A Kill also aborts the attempts in
// flight of the assertions it selects.
static void ApplyAssertionControlTask(const Expr* expr, SimContext& ctx,
                                      Arena& arena, std::string_view name) {
  auto arg_or = [&](size_t i, uint32_t fallback) {
    if (i >= expr->args.size() || expr->args[i] == nullptr) return fallback;
    return static_cast<uint32_t>(
        EvalExpr(expr->args[i], ctx, arena).ToUint64());
  };
  AssertControlCall call;
  size_t levels_at = 0;
  if (name == "$assertcontrol") {
    if (expr->args.empty() || expr->args[0] == nullptr) return;
    call.control_type = arg_or(0, 0);
    call.assertion_type = arg_or(1, kAssertionTypeDefault);
    call.directive_type = arg_or(2, kDirectiveTypeDefault);
    levels_at = 3;
  } else {
    AssertControlInvocation inv;
    if (!EquivalentAssertControlForTask(name, inv)) return;
    call.control_type = inv.control_type;
    call.assertion_type = inv.assertion_type;
    call.directive_type = inv.directive_type;
  }
  call.levels = arg_or(levels_at, 0);
  std::string caller;
  if (expr->args.size() > levels_at + 1) caller = ScopeHierName(ctx);
  for (size_t i = levels_at + 1; i < expr->args.size(); ++i) {
    if (expr->args[i] != nullptr) {
      call.scopes.push_back(ScopeItemNames(expr->args[i], caller));
    }
  }
  if (call.control_type == static_cast<uint32_t>(AssertControlType::kKill)) {
    AbortKilledAttempts(call, ctx);
  }
  RaiseControlCallbacks(call, ctx);
  ctx.AssertControls().Apply(std::move(call));
}

// §16.5.1's sampled value of `arg`: the store answers a variable read with the
// value it had in the Preponed region of this time slot while the mode below is
// raised, which is what §16.9.3 makes $sampled and every value-change function
// read. The previous setting is put back rather than cleared, so a sampled
// value function called from inside a property's own evaluation leaves that
// evaluation sampled.
Logic4Vec EvalSampledArg(const Expr* arg, SimContext& ctx, Arena& arena) {
  auto& samples = ctx.AssertionSamples();
  bool outer = samples.EvaluatingProperty();
  samples.SetEvaluatingProperty(true);
  auto value = EvalExpr(arg, ctx, arena);
  samples.SetEvaluatingProperty(outer);
  return value;
}

// §16.9.3's answer for a value-change function called no later than the time
// step of the first clocking event: the comparison is against the expression's
// default sampled value, which §16.5.1 makes the value its declaration assigned
// or the uninitialized value of its type.
static Logic4Vec EvalDefaultSampledArg(const Expr* arg, SimContext& ctx,
                                       Arena& arena) {
  auto& samples = ctx.AssertionSamples();
  bool outer = samples.EvaluatingProperty();
  samples.SetEvaluatingProperty(true);
  samples.SetReadingDefaults(true);
  auto value = EvalExpr(arg, ctx, arena);
  samples.SetReadingDefaults(false);
  samples.SetEvaluatingProperty(outer);
  return value;
}

// Whether the least significant bit is the known value `one`. §16.9.3's $rose
// and $fell are written on that bit alone -- $rose asks whether the
// expression's LSB went to 1 -- and an x or a z is neither 1 nor 0, so a bit
// carrying one is answered no by both questions.
static bool LsbIs(const Logic4Vec& v, bool one) {
  if (v.nwords == 0) return false;
  if ((v.words[0].bval & 1) != 0) return false;
  return ((v.words[0].aval & 1) != 0) == one;
}

// Whether two sampled values differ, which is the question §16.9.3 asks of
// $stable and $changed, whether the expression's value stayed the same. Every
// bit counts, including the x and z a 4-state value carries, so the comparison
// is over both planes rather than through a numeric projection.
static bool SampledValuesDiffer(const Logic4Vec& a, const Logic4Vec& b) {
  if (a.width != b.width) return true;
  for (uint32_t i = 0; i < a.nwords && i < b.nwords; ++i) {
    if (a.words[i].aval != b.words[i].aval) return true;
    if (a.words[i].bval != b.words[i].bval) return true;
  }
  return false;
}

// §16.9.3's four value-change functions, each answering 1'b1 or 1'b0 from the
// sampled value now and the one at the prior clock tick.
static Logic4Vec ValueChangeAnswer(std::string_view name,
                                   const Logic4Vec& now_val,
                                   const Logic4Vec& prev_val, Arena& arena) {
  bool result = false;
  if (name == "$rose" || name == "$rose_gclk") {
    result = LsbIs(now_val, true) && !LsbIs(prev_val, true);
  } else if (name == "$fell" || name == "$fell_gclk") {
    result = LsbIs(now_val, false) && !LsbIs(prev_val, false);
  } else if (name == "$stable" || name == "$stable_gclk") {
    result = !SampledValuesDiffer(now_val, prev_val);
  } else {
    result = SampledValuesDiffer(now_val, prev_val);
  }
  return MakeLogic4VecVal(arena, 1, result ? 1 : 0);
}

// §16.9.3: the number_of_ticks argument of $past, which is a constant and is 1
// where the call leaves it empty.
static uint32_t PastTickCount(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2 || expr->args[1] == nullptr) return 1;
  auto n = EvalExpr(expr->args[1], ctx, arena).ToUint64();
  return n == 0 ? 1 : static_cast<uint32_t>(n);
}

// §16.9/§16.13: the sampled-value functions and immediate-assertion-control
// queries. Returns the result when `name` selects one of these, or nullopt so
// the caller can fall through to the other system-call families.
//
// §16.9.3's functions are keyed by their own call site. Each is evaluated once
// per tick of the clock it samples on -- the assertion's clock where it is
// written in one, the procedure's where it is not -- so the value the site saw
// last is the expression's sampled value at the latest earlier time step that
// held a clocking event, which is what $past returns and what the four
// value-change functions compare against. Before the site has a history the
// clause names the comparison itself: the expression's default sampled value.
//
// §16.9.4's five future functions read a value sampled at the *next* global
// clock tick, which no evaluation standing at this one can read. What reaches
// them here is an evaluation that already stands at that next tick:
// ExecImmediateAssert samples the values of this tick and then waits for the
// global clocking event before evaluating the property, so the argument's
// current sampled value is the future one the clause names and the value at the
// assertion's own tick is one tick back in the store.
static bool IsFutureSampledFunction(std::string_view name) {
  return name == "$future_gclk" || name == "$rising_gclk" ||
         name == "$falling_gclk" || name == "$steady_gclk" ||
         name == "$changing_gclk";
}

// §16.9.3's $past and §16.9.4's global-clocking spelling of it, which take the
// value from a stated number of clock ticks back.
static bool IsPastSampledFunction(std::string_view name) {
  return name == "$past" || name == "$past_gclk";
}

// §16.9.3's four value change functions and the global-clocking spellings that
// look back rather than forward.
static bool IsValueChangeFunction(std::string_view name) {
  return name == "$rose" || name == "$fell" || name == "$stable" ||
         name == "$changed" || name == "$rose_gclk" || name == "$fell_gclk" ||
         name == "$stable_gclk" || name == "$changed_gclk";
}

// §16.9.3's two past-directed shapes: $past's own value from a stated number of
// ticks back, and the four value-change answers, which take one tick back. Both
// read the history this call site has and record what it sampled now, and both
// fall back to the default sampled value the clause names for a site that has
// not been evaluated that many times yet.
// §16.9.3: `$past` may refer to automatic variables, its example reading
// `$past(b[i])` in a for loop over i and returning at each iteration the past
// value of the i-th bit, so one call site keeps one history per value its
// select indices take: the indices of every select in the argument, evaluated
// here, folded into one number. An argument with no select answers 0, the
// one history the site had.
//
// §11.12 with §16.9.3: a let's body is expanded at each of its instances, so
// a sampled value call there is one call per instance, each with a history of
// its own; the instance (CurrentLetInstance) is folded in first.
static uint64_t ArgumentVariant(const Expr* arg, SimContext& ctx,
                                Arena& arena) {
  uint64_t variant = CurrentLetInstance();
  ForEachSubExpr(arg, [&](const Expr* e) {
    if (e->kind != ExprKind::kSelect || e->index == nullptr) return;
    uint64_t index = EvalExpr(e->index, ctx, arena).ToUint64();
    variant = variant * 1000003u + index + 1;
  });
  return variant;
}

// §16.9.3: `expression2` of $past gates the clocking event, the sampling of
// expression1 being based on the clock `iff expression2`, so a tick at which
// the gate is false is neither recorded nor counted among the ticks looked
// back over. An absent gate defaults to 1'b1.
static bool PastGateOpen(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 3 || expr->args[2] == nullptr) return true;
  return EvalSampledArg(expr->args[2], ctx, arena).IsTruthy();
}

// §16.5.1: whether `arg` reads an event's or a sequence's `triggered`, or a
// sequence's `matched`, a past value of which a sampled value function takes
// from the Postponed region of the past tick.
static bool ReadsEndPointMethod(const Expr* arg) {
  bool found = false;
  ForEachSubExpr(arg, [&](const Expr* e) {
    if (e->kind == ExprKind::kMemberAccess &&
        (e->rhs->text == "triggered" || e->rhs->text == "matched")) {
      found = true;
    }
  });
  return found;
}

// §16.5.1: this tick's entry in the history of `site` becomes the value
// `arg` has in the Postponed region of the tick, read in the process and the
// scopes the call is evaluated in, over the one recorded in the Observed
// region.
static void RecordPostponedSample(const Expr* arg, const SampleSite& site,
                                  uint32_t ticks, SimContext& ctx,
                                  Arena& arena) {
  PendingReportScope scope = PendingReportScope::Capture(ctx);
  auto* ev = ctx.GetScheduler().GetEventPool().Acquire();
  ev->callback = [arg, site, ticks, scope, &ctx, &arena]() {
    PendingReportScope saved;
    scope.Install(ctx, saved);
    Logic4Vec value = EvalSampledArg(arg, ctx, arena);
    ctx.AssertionSamples().RecordTick(site, value, ticks, arena);
    PendingReportScope::Restore(ctx, saved);
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kPostponed, ev);
}

static Logic4Vec EvalPastOrValueChange(const Expr* expr, SimContext& ctx,
                                       Arena& arena, std::string_view name,
                                       const Logic4Vec& now_val) {
  auto& samples = ctx.AssertionSamples();
  bool is_past = IsPastSampledFunction(name);
  // §16.9.3 (printed pages 415 and 417): given a clocking event of its own, a
  // value change function compares the sampled value now with the one at the
  // most recent strictly prior tick of that event, which the call site's
  // monitor records (Lowerer::LowerSampledClockMonitors), and before the
  // first such tick with the default sampled value.
  if (!is_past && expr->sampled_clock != nullptr) {
    const Logic4Vec* prior =
        samples.PastValue(SampleSite{expr, 0, ctx.CurrentTime().ticks}, 1);
    Logic4Vec prev_val = prior != nullptr
                             ? *prior
                             : EvalDefaultSampledArg(expr->args[0], ctx, arena);
    return ValueChangeAnswer(name, now_val, prev_val, arena);
  }
  uint32_t ticks = is_past ? PastTickCount(expr, ctx, arena) : 1;
  SampleSite site{expr, ArgumentVariant(expr->args[0], ctx, arena),
                  ctx.CurrentTime().ticks};
  // This tick's sample is recorded first, once per time step however often
  // the site is evaluated in it, and the value asked for is read behind it.
  if (!is_past || PastGateOpen(expr, ctx, arena)) {
    samples.RecordTick(site, now_val, ticks, arena);
    if (ReadsEndPointMethod(expr->args[0])) {
      RecordPostponedSample(expr->args[0], site, ticks, ctx, arena);
    }
  }
  const Logic4Vec* past = samples.PastValue(site, ticks);
  Logic4Vec prev_val = past != nullptr
                           ? *past
                           : EvalDefaultSampledArg(expr->args[0], ctx, arena);
  if (is_past) return prev_val;
  return ValueChangeAnswer(name, now_val, prev_val, arena);
}

// §16.9.4's four future predicates, each defined against §16.9.3's own
// value-change function of the same shape: $rising_gclk asks whether the
// sampled LSB of the expression goes to 1 at the next global clocking tick,
// which is $rose over the pair (next tick, this tick), and
// $falling_gclk, $steady_gclk and $changing_gclk stand in the same relation to
// $fell, $stable and $changed. Naming the analogue rather than restating the
// rule keeps the x and z handling of LsbIs and SampledValuesDiffer answering
// both clauses.
static std::string_view PastAnalogueOfFutureFunction(std::string_view name) {
  if (name == "$rising_gclk") return "$rose";
  if (name == "$falling_gclk") return "$fell";
  if (name == "$steady_gclk") return "$stable";
  return "$changed";
}

// §16.9.4's five future functions, evaluated at the global clock tick that
// follows the assertion's own, with what was sampled at that tick installed
// (see FutureGclkAttemptCoroutine in stmt_exec_deferred.cpp). The argument's
// sampled value here, read past that snapshot, is the one the clause calls the
// value at the next global clock tick, and read through it, the value at the
// assertion's tick. An evaluation with none installed did not go through that
// wait, and the clause's own fallback for a comparison with no prior tick is
// the expression's default sampled value.
static Logic4Vec EvalFutureGclk(const Expr* expr, SimContext& ctx, Arena& arena,
                                std::string_view name) {
  if (expr->args.empty() || expr->args[0] == nullptr) {
    return MakeLogic4VecVal(arena, name == "$future_gclk" ? 32 : 1, 0);
  }
  auto& samples = ctx.AssertionSamples();
  const AssertionSampleStore::Snapshot* own_tick = samples.InstalledSnapshot();
  samples.SetSnapshot(nullptr);
  auto next_val = EvalSampledArg(expr->args[0], ctx, arena);
  samples.SetSnapshot(own_tick);
  if (name == "$future_gclk") return next_val;
  Logic4Vec cur_val = own_tick != nullptr
                          ? EvalSampledArg(expr->args[0], ctx, arena)
                          : EvalDefaultSampledArg(expr->args[0], ctx, arena);
  return ValueChangeAnswer(PastAnalogueOfFutureFunction(name), next_val,
                           cur_val, arena);
}

// §16.9.3's $sampled and its past-directed functions, which all read the
// argument's sampled value at this tick: $sampled returns it, and $past and the
// four value-change functions compare it with what the site saw before. A call
// written with no argument is answered with a zero of the width the function
// carries -- one bit for $sampled's Boolean, the default integer width for the
// value $past returns -- rather than left to read args[0].
static Logic4Vec EvalSampledOrPast(const Expr* expr, SimContext& ctx,
                                   Arena& arena, std::string_view name) {
  bool is_sampled = name == "$sampled";
  if (expr->args.empty() || expr->args[0] == nullptr) {
    return MakeLogic4VecVal(arena, is_sampled ? 1 : 32, 0);
  }
  auto now_val = EvalSampledArg(expr->args[0], ctx, arena);
  if (is_sampled) return now_val;
  return EvalPastOrValueChange(expr, ctx, arena, name, now_val);
}

static std::optional<Logic4Vec> EvalSampledValueFunc(const Expr* expr,
                                                     SimContext& ctx,
                                                     Arena& arena,
                                                     std::string_view name) {
  if (name == "$sampled" || IsPastSampledFunction(name) ||
      IsValueChangeFunction(name)) {
    return EvalSampledOrPast(expr, ctx, arena, name);
  }
  if (IsFutureSampledFunction(name)) {
    return EvalFutureGclk(expr, ctx, arena, name);
  }
  return std::nullopt;
}

static std::optional<Logic4Vec> EvalSampledValueOrAssert(
    const Expr* expr, SimContext& ctx, Arena& arena, std::string_view name) {
  if (auto sampled = EvalSampledValueFunc(expr, ctx, arena, name))
    return sampled;

  if (IsAssertionControlTaskName(name)) {
    // §20.11: an assertion control system task takes effect when executed; the
    // call itself yields no meaningful value.
    ApplyAssertionControlTask(expr, ctx, arena, name);
    return MakeLogic4VecVal(arena, 1, 0);
  }

  return std::nullopt;
}

Logic4Vec EvalVerifSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           std::string_view name) {
  if (auto sampled = EvalSampledValueOrAssert(expr, ctx, arena, name))
    return *sampled;

  if (auto coverage = EvalCoverageSysCall(expr, ctx, arena, name))
    return *coverage;

  if (name.starts_with("$q_"))
    return EvalStochasticQueue(expr, ctx, arena, name);

  return MakeLogic4VecVal(arena, 32, 0);
}

}  // namespace delta
