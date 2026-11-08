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

enum QueueStatus : std::uint8_t {
  kQOk = 0,
  kQFullCannotAdd = 1,
  kQUndefinedId = 2,
  kQEmptyCannotRemove = 3,
  kQUnsupportedType = 4,
  kQNonPositiveLength = 5,
  kQDuplicateId = 6,
};

using QueueArgList = std::vector<Expr*>;
using StochasticQueueMap = std::unordered_map<uint64_t, StochasticQueue>;

static int64_t QueueSignedArg(const Logic4Vec& v) {
  uint64_t raw = v.ToUint64();
  uint32_t w = v.width;
  if (w == 0 || w >= 64) return static_cast<int64_t>(raw);
  uint64_t sign_bit = 1ull << (w - 1);
  if (raw & sign_bit) raw |= ~((1ull << w) - 1);
  return static_cast<int64_t>(raw);
}

static void WriteQueueStatus(const Expr* status_arg, uint64_t status,
                             SimContext& ctx, Arena& arena) {
  if (!status_arg || status_arg->kind != ExprKind::kIdentifier) return;
  auto* var = ctx.FindVariable(status_arg->text);
  if (var) {
    var->value = MakeLogic4VecVal(arena, var->value.width, status);
    var->NotifyWatchers();
  }
}

static void WriteQueueOutput(const Expr* out_arg, uint64_t value,
                             SimContext& ctx, Arena& arena) {
  if (!out_arg || out_arg->kind != ExprKind::kIdentifier) return;
  auto* var = ctx.FindVariable(out_arg->text);
  if (var) {
    var->value = MakeLogic4VecVal(arena, var->value.width, value);
    var->NotifyWatchers();
  }
}

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
    uint64_t job_id = EvalExpr(args[1], ctx, arena).ToUint64();
    uint64_t inform_id = EvalExpr(args[2], ctx, arena).ToUint64();
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

static uint64_t QueueExamStatistic(const StochasticQueue& q, int64_t code,
                                   uint64_t now) {
  switch (code) {
    case 1:
      return q.count;
    case 2:
      return q.arrivals > 1 ? (q.last_arrival_tick - q.first_arrival_tick) /
                                  (q.arrivals - 1)
                            : 0;
    case 3:
      return q.max_count;
    case 4:
      return q.departures ? q.shortest_wait : 0;
    case 5:
      return q.entries.empty() ? 0
                               : (now >= q.entries.front().arrival_tick
                                      ? now - q.entries.front().arrival_tick
                                      : 0);
    case 6:
      return q.departures ? q.total_wait / q.departures : 0;
    default:
      return 0;
  }
}

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

Logic4Vec EvalSampledArg(const Expr* arg, SimContext& ctx, Arena& arena) {
  auto& samples = ctx.AssertionSamples();
  bool outer = samples.EvaluatingProperty();
  samples.SetEvaluatingProperty(true);
  auto value = EvalExpr(arg, ctx, arena);
  samples.SetEvaluatingProperty(outer);
  return value;
}

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

static bool LsbIs(const Logic4Vec& v, bool one) {
  if (v.nwords == 0) return false;
  if ((v.words[0].bval & 1) != 0) return false;
  return ((v.words[0].aval & 1) != 0) == one;
}

static bool SampledValuesDiffer(const Logic4Vec& a, const Logic4Vec& b) {
  if (a.width != b.width) return true;
  for (uint32_t i = 0; i < a.nwords && i < b.nwords; ++i) {
    if (a.words[i].aval != b.words[i].aval) return true;
    if (a.words[i].bval != b.words[i].bval) return true;
  }
  return false;
}

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

static uint32_t PastTickCount(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2 || expr->args[1] == nullptr) return 1;
  auto n = EvalExpr(expr->args[1], ctx, arena).ToUint64();
  return n == 0 ? 1 : static_cast<uint32_t>(n);
}

static bool IsFutureSampledFunction(std::string_view name) {
  return name == "$future_gclk" || name == "$rising_gclk" ||
         name == "$falling_gclk" || name == "$steady_gclk" ||
         name == "$changing_gclk";
}

static bool IsPastSampledFunction(std::string_view name) {
  return name == "$past" || name == "$past_gclk";
}

static bool IsValueChangeFunction(std::string_view name) {
  return name == "$rose" || name == "$fell" || name == "$stable" ||
         name == "$changed" || name == "$rose_gclk" || name == "$fell_gclk" ||
         name == "$stable_gclk" || name == "$changed_gclk";
}

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

static bool PastGateOpen(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 3 || expr->args[2] == nullptr) return true;
  return EvalSampledArg(expr->args[2], ctx, arena).IsTruthy();
}

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

static std::string_view PastAnalogueOfFutureFunction(std::string_view name) {
  if (name == "$rising_gclk") return "$rose";
  if (name == "$falling_gclk") return "$fell";
  if (name == "$steady_gclk") return "$stable";
  return "$changed";
}

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
