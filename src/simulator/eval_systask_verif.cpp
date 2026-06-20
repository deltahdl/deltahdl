#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/coverage_control.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
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
  if (var) var->value = MakeLogic4VecVal(arena, var->value.width, status);
}

// §20.15.3: write an integer value back through one of $q_remove's output
// arguments (job_id, inform_id), keeping the destination variable's own width.
static void WriteQueueOutput(const Expr* out_arg, uint64_t value,
                             SimContext& ctx, Arena& arena) {
  if (!out_arg || out_arg->kind != ExprKind::kIdentifier) return;
  auto* var = ctx.FindVariable(out_arg->text);
  if (var) var->value = MakeLogic4VecVal(arena, var->value.width, value);
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

  if (name == "$q_initialize") {
    if (args.size() < 4) return MakeLogic4VecVal(arena, 32, 0);
    uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
    int64_t q_type = QueueSignedArg(EvalExpr(args[1], ctx, arena));
    int64_t max_length = QueueSignedArg(EvalExpr(args[2], ctx, arena));
    uint64_t status;
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

  if (name == "$q_add") {
    if (args.size() < 4) return MakeLogic4VecVal(arena, 32, 0);
    uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
    auto it = queues.find(q_id);
    uint64_t status;
    if (it == queues.end()) {
      status = kQUndefinedId;
    } else if (static_cast<int64_t>(it->second.count) >=
               it->second.max_length) {
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

  if (name == "$q_remove") {
    // §20.15.3 $q_remove(q_id, job_id, inform_id, status): take an entry off
    // the queue selected by q_id (an integer input) and report the removed
    // entry's identifiers through the job_id and inform_id outputs.
    if (args.size() < 4) return MakeLogic4VecVal(arena, 32, 0);
    uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
    auto it = queues.find(q_id);
    uint64_t status;
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

  if (name == "$q_full") {
    // §20.15.4: $q_full checks whether the queue named by q_id has room for
    // another entry, returning 1 when it is full and 0 when it is not. A queue
    // is full once its occupancy reaches the capacity fixed at $q_initialize.
    // The trailing status reports the operation outcome (§20.15.6); the only
    // error condition that applies is an undefined q_id.
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

  if (name == "$q_exam") {
    // §20.15.5 $q_exam(q_id, q_stat_code, q_stat_value, status): report a
    // statistic about activity on the queue named by q_id. The q_stat_code
    // selects which statistic is delivered through the q_stat_value output, per
    // Table 20-10. An undefined q_id is the only applicable error (§20.15.6).
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
    uint64_t value = 0;
    switch (code) {
      case 1:  // Current queue length.
        value = q.count;
        break;
      case 2:  // Mean interarrival time: total span between the first and last
               // arrival divided by the number of gaps between arrivals.
        value = q.arrivals > 1 ? (q.last_arrival_tick - q.first_arrival_tick) /
                                     (q.arrivals - 1)
                               : 0;
        break;
      case 3:  // Maximum queue length ever reached.
        value = q.max_count;
        break;
      case 4:  // Shortest wait time ever, across removed entries.
        value = q.departures ? q.shortest_wait : 0;
        break;
      case 5:  // Longest wait among entries still queued: the oldest entry is
               // at the front, as $q_add appends in arrival order.
        value = q.entries.empty() ? 0
                                  : (now >= q.entries.front().arrival_tick
                                         ? now - q.entries.front().arrival_tick
                                         : 0);
        break;
      case 6:  // Average wait time over removed entries.
        value = q.departures ? q.total_wait / q.departures : 0;
        break;
      default:
        value = 0;
        break;
    }
    WriteQueueOutput(args[2], value, ctx, arena);
    WriteQueueStatus(args[3], kQOk, ctx, arena);
    return MakeLogic4VecVal(arena, 32, kQOk);
  }

  return MakeLogic4VecVal(arena, 32, 0);
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
  if (expr->args.empty()) return status_vec(CoverageStatus::Error);
  int control_value =
      static_cast<int>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  CoverageControl control;
  if (!CoverageControlFromInt(control_value, &control)) {
    return status_vec(CoverageStatus::Error);
  }
  // The fourth argument names the module definition or instance. When given as
  // a string literal it is used directly; otherwise the scope is left empty.
  std::string scope;
  if (expr->args.size() > 3 &&
      expr->args[3]->kind == ExprKind::kStringLiteral) {
    scope = ExtractStrArg(expr->args[3]);
  }
  return status_vec(ctx.GetCoverageControlState().Control(control, scope));
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
    return CoverageIntResult(arena, static_cast<int>(CoverageStatus::Error));
  }
  int coverage_type =
      static_cast<int>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  std::string str_arg = CoverageStrArg(expr, str_arg_index);
  auto& state = ctx.GetCoverageControlState();
  switch (query) {
    case CoverageQuery::kGetMax:
      return CoverageIntResult(arena,
                               state.CoverageMax(str_arg, coverage_type));
    case CoverageQuery::kGet:
      return CoverageIntResult(arena,
                               state.CoverageGet(str_arg, coverage_type));
    case CoverageQuery::kMerge:
      return CoverageIntResult(
          arena, static_cast<int>(state.CoverageMerge(coverage_type, str_arg)));
    case CoverageQuery::kSave:
      return CoverageIntResult(
          arena, static_cast<int>(state.CoverageSave(coverage_type, str_arg)));
  }
  return CoverageIntResult(arena, static_cast<int>(CoverageStatus::Error));
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

Logic4Vec EvalVerifSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           std::string_view name) {
  if (name == "$sampled") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
    return EvalExpr(expr->args[0], ctx, arena);
  }
  if (name == "$past") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
    return EvalExpr(expr->args[0], ctx, arena);
  }
  if (name == "$rose" || name == "$fell" || name == "$stable" ||
      name == "$changed") {
    return MakeLogic4VecVal(arena, 1, 0);
  }

  // §16.9.4: $past_gclk(v) is defined as $past(v,,,@$global_clock) and
  // $future_gclk(v) is the value of v sampled at the next global clock tick;
  // both yield the (sampled) value of their argument.
  if (name == "$past_gclk" || name == "$future_gclk") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
    return EvalExpr(expr->args[0], ctx, arena);
  }

  // §16.9.4: the global clocking value-change functions ($rose_gclk,
  // $fell_gclk, $stable_gclk, $changed_gclk and the future $rising_gclk,
  // $falling_gclk, $steady_gclk, $changing_gclk) each return a 1-bit Boolean.
  if (name.ends_with("_gclk")) {
    return MakeLogic4VecVal(arena, 1, 0);
  }

  if (name.starts_with("$assert")) return MakeLogic4VecVal(arena, 1, 0);

  if (name == "$coverage_control") return EvalCoverageControl(expr, ctx, arena);

  if (name == "$coverage_get_max") return EvalCoverageGetMax(expr, ctx, arena);

  if (name == "$coverage_get") return EvalCoverageGet(expr, ctx, arena);

  if (name == "$coverage_merge") return EvalCoverageMerge(expr, ctx, arena);

  if (name == "$coverage_save") return EvalCoverageSave(expr, ctx, arena);

  if (name.starts_with("$coverage")) return MakeLogic4VecVal(arena, 32, 0);

  if (name.starts_with("$q_"))
    return EvalStochasticQueue(expr, ctx, arena, name);

  return MakeLogic4VecVal(arena, 32, 0);
}

}  // namespace delta
