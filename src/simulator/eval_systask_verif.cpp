#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "parser/assertion_control_task.h"
#include "parser/ast.h"
#include "simulator/coverage_control.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"
#include "simulator/variable.h"

namespace delta {

// §20.15.6 Table 20-11 status code values returned through the trailing
// `status` output argument of every stochastic-analysis queue task and
// function. Value 7 ("not enough memory, cannot create queue") is defined by
// the table but has no deterministic trigger in the model, so nothing emits
// it.
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
  // §9.4.2: "A non-edge implicit event shall be detected on any change in the
  // value of the expression", and the clause names no writer whose change is
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

// §40.3.2.1 Table 40-2: the scope_def argument beside the scope says how far
// the call reaches - `SV_COV_HIER over "the named instance and any hierarchy
// below it", `SV_COV_MODULE over that instance alone, "excluding any hierarchy
// in instances below that instance". The two are the §40.3.1 constants 11 and
// 10; nothing else names a scope definition, and a call that wrote something
// else wrote a bad argument.
constexpr int kSvCovModule = 10;
constexpr int kSvCovHier = 11;

static bool CoverageScopeDefIncludesBelow(const Expr* expr, SimContext& ctx,
                                          Arena& arena, size_t index,
                                          bool* include_below) {
  if (expr->args.size() <= index) return false;
  int scope_def =
      static_cast<int>(EvalExpr(expr->args[index], ctx, arena).ToUint64());
  if (scope_def == kSvCovHier) {
    *include_below = true;
    return true;
  }
  if (scope_def == kSvCovModule) {
    *include_below = false;
    return true;
  }
  return false;
}

// §40.3.2.1: $coverage_control(control_constant, coverage_type, scope_def,
// modules_or_instance) performs the control action named by its first argument
// over the scope named by its fourth and returns one of the §40.3.1 status
// values. The action is applied to the simulation's coverage-control state.
static Logic4Vec EvalCoverageControl(const Expr* expr, SimContext& ctx,
                                     Arena& arena) {
  auto status_vec = [&](CoverageStatus status) {
    return MakeLogic4VecVal(arena, 32,
                            static_cast<uint32_t>(static_cast<int>(status)));
  };
  // A control constant outside the §40.3.1 set (or a missing one) is a bad
  // argument, reported as `SV_COV_ERROR.
  if (expr->args.empty()) return status_vec(CoverageStatus::kError);
  int control_value =
      static_cast<int>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  CoverageControl control{};
  if (!CoverageControlFromInt(control_value, &control)) {
    return status_vec(CoverageStatus::kError);
  }
  // §40.3.2.1 Table 40-2: the third argument says whether the hierarchy below
  // the named scope is controlled with it. A scope definition the clause does
  // not name is a bad argument, which is the `SV_COV_ERROR the clause reports
  // "on all operations ... typically due to errors in arguments".
  bool include_below = true;
  if (!CoverageScopeDefIncludesBelow(expr, ctx, arena, 2, &include_below)) {
    return status_vec(CoverageStatus::kError);
  }
  // The fourth argument names the module definition or instance. When given as
  // a string literal it is used directly; otherwise the scope is left empty.
  std::string scope;
  if (expr->args.size() > 3 &&
      expr->args[3]->kind == ExprKind::kStringLiteral) {
    scope = ExtractStrArg(expr->args[3]);
  }
  return status_vec(
      ctx.GetCoverageControlState().Control(control, scope, include_below));
}

// Builds the 32-bit integer coverage result shared by the §40.3.2 query
// functions ($coverage_get_max/$coverage_get/$coverage_merge/$coverage_save),
// whose result is always one of the §40.3.1 status values or a positive count.
static Logic4Vec CoverageIntResult(Arena& arena, int value) {
  return MakeLogic4VecVal(arena, 32, static_cast<uint32_t>(value));
}

// Extracts the optional string literal argument (scope name or coverage
// database name) at `index`. A missing or non-literal argument yields the empty
// string, matching each §40.3.2 query function's "left empty" fallback.
static std::string CoverageStrArg(const Expr* expr, size_t index) {
  if (expr->args.size() > index &&
      expr->args[index]->kind == ExprKind::kStringLiteral) {
    return ExtractStrArg(expr->args[index]);
  }
  return std::string();
}

// Shared evaluator for the §40.3.2 coverage query functions. They all return
// the §40.3.2.2 integer result pattern: `SV_COV_ERROR when the first
// (coverage_type) argument is missing, otherwise the value produced by `query`
// from the coverage type and the optional string argument (scope/name) at
// `str_arg_index`.
enum class CoverageQuery : std::uint8_t { kGetMax, kGet, kMerge, kSave };
static Logic4Vec EvalCoverageQuery(const Expr* expr, SimContext& ctx,
                                   Arena& arena, CoverageQuery query,
                                   size_t str_arg_index) {
  // The first argument selects the coverage type; without it the arguments are
  // incorrect, reported as `SV_COV_ERROR.
  if (expr->args.empty()) {
    return CoverageIntResult(arena, static_cast<int>(CoverageStatus::kError));
  }
  int coverage_type =
      static_cast<int>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  std::string str_arg = CoverageStrArg(expr, str_arg_index);
  // §40.3.2.1 Table 40-2 governs the two hierarchy queries too: their second
  // argument is the same scope_def. The database queries of §40.3.2.4/.5 name
  // no scope, so they have none to read and none to refuse.
  bool include_below = true;
  bool queries_a_scope =
      query == CoverageQuery::kGetMax || query == CoverageQuery::kGet;
  if (queries_a_scope &&
      !CoverageScopeDefIncludesBelow(expr, ctx, arena, 1, &include_below)) {
    return CoverageIntResult(arena, static_cast<int>(CoverageStatus::kError));
  }
  auto& state = ctx.GetCoverageControlState();
  switch (query) {
    case CoverageQuery::kGetMax:
      return CoverageIntResult(
          arena, state.CoverageMax(str_arg, coverage_type, include_below));
    case CoverageQuery::kGet:
      return CoverageIntResult(
          arena, state.CoverageGet(str_arg, coverage_type, include_below));
    case CoverageQuery::kMerge:
      return CoverageIntResult(
          arena, static_cast<int>(state.CoverageMerge(coverage_type, str_arg)));
    case CoverageQuery::kSave:
      return CoverageIntResult(
          arena, static_cast<int>(state.CoverageSave(coverage_type, str_arg)));
  }
  return CoverageIntResult(arena, static_cast<int>(CoverageStatus::kError));
}

// §40.3.2.2: $coverage_get_max(coverage_type, scope_def, modules_or_instance)
// returns the value representing 100% coverage for the given coverage type over
// the named hierarchy — the sum of all coverable items of that type. The value
// is a property of the design and stays constant for the whole simulation. The
// integer result is one of the §40.3.1 status values (`SV_COV_ERROR for bad
// arguments, `SV_COV_NOCOV when no coverage is available, `SV_COV_OVERFLOW when
// the count is too large to represent) or a positive maximum coverage number.
// The third argument names the module definition or instance, as the scope is
// specified per $coverage_control() (§40.3.2.1).
static Logic4Vec EvalCoverageGetMax(const Expr* expr, SimContext& ctx,
                                    Arena& arena) {
  return EvalCoverageQuery(expr, ctx, arena, CoverageQuery::kGetMax,
                           /*str_arg_index=*/2);
}

// §40.3.2.3: $coverage_get(coverage_type, scope_def, modules_or_instance)
// returns the current coverage value for the given coverage type over the named
// hierarchy — the number of coverable items of that type covered so far. It
// follows the same return pattern as $coverage_get_max() (§40.3.2.2), but the
// positive value is the current coverage level rather than the maximum, so
// coverage% is coverage_get()/coverage_get_max() * 100. The integer result is
// one of the §40.3.1 status values (`SV_COV_ERROR for bad arguments,
// `SV_COV_NOCOV when no coverage is available, `SV_COV_OVERFLOW when the count
// is too large to represent) or a positive current coverage number.
static Logic4Vec EvalCoverageGet(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  return EvalCoverageQuery(expr, ctx, arena, CoverageQuery::kGet,
                           /*str_arg_index=*/2);
}

// §40.3.2.4: $coverage_merge(coverage_type, "name") loads and merges coverage
// data of the given coverage type from the named coverage database into the
// simulation. `name` is an arbitrary, implementation-specific locator for the
// database. The integer result is one of the §40.3.1 status values:
// `SV_COV_OK when the data are found (for this design) and merged,
// `SV_COV_NOCOV when the data are found but do not contain the requested
// coverage type, and `SV_COV_ERROR when the name does not exist, the data are
// from a different design, or another error occurs. A missing or non-literal
// name locates no database, which is the error case.
static Logic4Vec EvalCoverageMerge(const Expr* expr, SimContext& ctx,
                                   Arena& arena) {
  return EvalCoverageQuery(expr, ctx, arena, CoverageQuery::kMerge,
                           /*str_arg_index=*/1);
}

// §40.3.2.5: $coverage_save(coverage_type, "name") saves the current coverage
// of the given type to the tool's coverage database under `name`, so a later
// $coverage_merge() (§40.3.2.4) with the same name can load it. Saving never
// affects the coverage state of this simulation. The integer result is one of
// the §40.3.1 status values: `SV_COV_OK when the data are saved, `SV_COV_NOCOV
// when no such coverage is available in this design (nothing is saved), and
// `SV_COV_ERROR when an error occurs during the save — in which case the entry
// for `name` is removed to preserve coverage-database integrity. A missing or
// non-literal name leaves the destination empty.
static Logic4Vec EvalCoverageSave(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  return EvalCoverageQuery(expr, ctx, arena, CoverageQuery::kSave,
                           /*str_arg_index=*/1);
}

// §20.11: apply an assertion control system task that names no scope list, so
// it affects the whole design (the LRM's own examples note that whole-design
// tasks name no modules). Only this whole-design form is modeled against
// immediate assertions, which are not registered by hierarchical name; a task
// that names specific scopes leaves them unaffected. On/Off/Kill toggle
// checking and FailOn/FailOff toggle the default fail action, each carrying the
// Table 20-6 assertion_type and Table 20-7 directive_type masks that select
// which assertions are affected.
static void ApplyGlobalAssertionControlTask(const Expr* expr, SimContext& ctx,
                                            Arena& arena,
                                            std::string_view name) {
  AssertControlInvocation inv;
  bool has_scope_list = false;
  if (name == "$assertcontrol") {
    // Argument order: control_type, assertion_type, directive_type, levels,
    // then the scope list. control_type is required; the type masks default to
    // 255 and 7 when omitted.
    if (expr->args.empty() || !expr->args[0]) return;
    inv.control_type =
        static_cast<uint32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
    inv.assertion_type =
        (expr->args.size() > 1 && expr->args[1])
            ? static_cast<uint32_t>(
                  EvalExpr(expr->args[1], ctx, arena).ToUint64())
            : kAssertionTypeDefault;
    inv.directive_type =
        (expr->args.size() > 2 && expr->args[2])
            ? static_cast<uint32_t>(
                  EvalExpr(expr->args[2], ctx, arena).ToUint64())
            : kDirectiveTypeDefault;
    has_scope_list = expr->args.size() > 4;  // levels at [3], scopes at [4..]
  } else {
    // A convenience/backward-compatibility task expands to a fixed
    // $assertcontrol invocation; its own arguments are (levels, scope...).
    if (!EquivalentAssertControlForTask(name, inv)) return;
    has_scope_list = expr->args.size() > 1;
  }
  if (has_scope_list) return;

  switch (static_cast<AssertControlType>(inv.control_type)) {
    case AssertControlType::kOn:
      // §20.11: On re-enables checking and violation reporting.
      ctx.SetGlobalAssertCheckingOn();
      ctx.SetGlobalAssertFailActionOn();
      break;
    case AssertControlType::kOff:
    case AssertControlType::kKill:
      // §20.11: Off/Kill stop the checking of the selected assertions.
      ctx.SetGlobalAssertCheckingOff(inv.assertion_type, inv.directive_type);
      break;
    case AssertControlType::kFailOn:
      ctx.SetGlobalAssertFailActionOn();
      break;
    case AssertControlType::kFailOff:
      // §20.11: FailOff stops the fail action, including the default $error.
      ctx.SetGlobalAssertFailActionOff(inv.assertion_type, inv.directive_type);
      break;
    default:
      // Lock/Unlock and the pass/vacuity action controls do not change
      // whole-design checking or the default fail action of immediate
      // assertions; their semantics are exercised on AssertionControl directly.
      break;
  }
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

// §16.9.3's answer for a value-change function called "at or before the
// simulation time step in which the first clocking event occurs": the
// comparison is against the expression's default sampled value, which §16.5.1
// makes the value its declaration assigned or the uninitialized value of its
// type.
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
// and $fell are written on that bit alone -- "the LSB of the expression changed
// to 1" -- and an x or a z is neither 1 nor 0, so a bit carrying one is
// answered no by both questions.
static bool LsbIs(const Logic4Vec& v, bool one) {
  if (v.nwords == 0) return false;
  if ((v.words[0].bval & 1) != 0) return false;
  return ((v.words[0].aval & 1) != 0) == one;
}

// Whether two sampled values differ, which is the question §16.9.3 asks of
// $stable and $changed: "the value of the expression did not change". Every bit
// counts, including the x and z a 4-state value carries, so the comparison is
// over both planes rather than through a numeric projection.
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

// §16.9.3: "number_of_ticks" of $past, which defaults to 1 -- "The default of 1
// is used for the empty number_of_ticks argument" -- and is a constant.
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
// last is "the sampled value of the expression from the most recent strictly
// prior time step in which the clocking event occurred", which is what $past
// returns and what the four value-change functions compare against. Before the
// site has a history the clause names the comparison itself: the expression's
// default sampled value.
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
static Logic4Vec EvalPastOrValueChange(const Expr* expr, SimContext& ctx,
                                       Arena& arena, std::string_view name,
                                       const Logic4Vec& now_val) {
  auto& samples = ctx.AssertionSamples();
  bool is_past = IsPastSampledFunction(name);
  uint32_t ticks = is_past ? PastTickCount(expr, ctx, arena) : 1;
  const Logic4Vec* past = samples.PastValue(expr, ticks);
  Logic4Vec prev_val = past != nullptr
                           ? *past
                           : EvalDefaultSampledArg(expr->args[0], ctx, arena);
  samples.RecordTick(expr, now_val, ticks, arena);
  if (is_past) return prev_val;
  return ValueChangeAnswer(name, now_val, prev_val, arena);
}

// §16.9.4's four future predicates, each defined against §16.9.3's own
// value-change function of the same shape: $rising_gclk is "the sampled value
// of the LSB of the expression is changing to 1 at the next global clocking
// tick", which is $rose over the pair (next tick, this tick), and
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
// follows the assertion's own. The argument's sampled value here is the one the
// clause calls the value at the next global clock tick; the value at the
// assertion's tick was sampled by the attempt at that tick and written into
// this call site's history just before this evaluation (see
// FutureGclkAttemptCoroutine in stmt_exec_deferred.cpp), so PastValue reads it
// back. A site with no history is one whose attempt did not go through that
// wait, and the clause's own fallback for a comparison with no prior tick is
// the expression's default sampled value.
static Logic4Vec EvalFutureGclk(const Expr* expr, SimContext& ctx, Arena& arena,
                                std::string_view name) {
  if (expr->args.empty() || expr->args[0] == nullptr) {
    return MakeLogic4VecVal(arena, name == "$future_gclk" ? 32 : 1, 0);
  }
  auto next_val = EvalSampledArg(expr->args[0], ctx, arena);
  if (name == "$future_gclk") return next_val;
  const Logic4Vec* at_tick = ctx.AssertionSamples().PastValue(expr, 1);
  Logic4Vec cur_val = at_tick != nullptr
                          ? *at_tick
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
    ApplyGlobalAssertionControlTask(expr, ctx, arena, name);
    return MakeLogic4VecVal(arena, 1, 0);
  }

  return std::nullopt;
}

// §40.3.2: the coverage query/control system functions. Returns the result
// when `name` is in the $coverage_* family, or nullopt otherwise.
static std::optional<Logic4Vec> EvalCoverageSysCall(const Expr* expr,
                                                    SimContext& ctx,
                                                    Arena& arena,
                                                    std::string_view name) {
  if (name == "$coverage_control") return EvalCoverageControl(expr, ctx, arena);

  if (name == "$coverage_get_max") return EvalCoverageGetMax(expr, ctx, arena);

  if (name == "$coverage_get") return EvalCoverageGet(expr, ctx, arena);

  if (name == "$coverage_merge") return EvalCoverageMerge(expr, ctx, arena);

  if (name == "$coverage_save") return EvalCoverageSave(expr, ctx, arena);

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
