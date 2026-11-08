#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "simulator/awaiters.h"
#include "simulator/contassign_delay.h"
#include "simulator/contassign_strength.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/interconnect_drive.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_contassign_driver.h"
#include "simulator/module_path_delay.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_sdf.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"

namespace delta {

static bool Logic4VecEqual(const Logic4Vec& a, const Logic4Vec& b) {
  if (a.nwords != b.nwords) return false;
  for (uint32_t i = 0; i < a.nwords; ++i) {
    if (a.words[i].aval != b.words[i].aval ||
        a.words[i].bval != b.words[i].bval)
      return false;
  }
  return true;
}

struct ContAssignDelayExprs {
  const Expr* rise = nullptr;
  const Expr* fall = nullptr;
  const Expr* decay = nullptr;
};

struct ContAssignParams {
  const Expr* lhs;
  const Expr* rhs;
  DriverStrength ds;
  ContAssignDelayExprs delays;
  uint32_t width = 0;
  ContAssignWhole whole;

  std::string inst_prefix;

  std::string interconnect_load;
  std::string interconnect_source;

  bool nonresistive_switch = false;

  bool resistive_switch = false;
  const Expr* data_input = nullptr;

  const Expr* three_state_ctrl = nullptr;
  const Expr* three_state_pass = nullptr;

  int64_t preset_driver = -1;

  std::string module_path_port;
  bool path_delayed_at_connection = false;
};

static ContAssignDelays BuildContAssignDelays(const ContAssignDelayExprs& exprs,
                                              SimContext& ctx, Arena& arena) {
  ContAssignDelays d;
  d.rise = DelayExprToTicks(exprs.rise, ctx, arena);
  d.fall = exprs.fall ? DelayExprToTicks(exprs.fall, ctx, arena) : 0;
  d.decay = exprs.decay ? DelayExprToTicks(exprs.decay, ctx, arena) : 0;
  d.has_fall = exprs.fall != nullptr;
  d.has_decay = exprs.decay != nullptr;
  return d;
}

enum class GateBit : uint8_t { kZero, kOne, kUnknown, kHighz };

static GateBit LowGateBit(const Logic4Vec& v) {
  if (v.nwords == 0) return GateBit::kUnknown;
  bool aval = (v.words[0].aval & 1) != 0;
  bool bval = (v.words[0].bval & 1) != 0;
  if (!bval) return aval ? GateBit::kOne : GateBit::kZero;
  return aval ? GateBit::kUnknown : GateBit::kHighz;
}

static DriverStrength ThreeStateGateStrength(const ContAssignParams& params,
                                             DriverStrength drive,
                                             SimContext& ctx, Arena& arena) {
  GateBit ctrl = LowGateBit(EvalExpr(params.three_state_ctrl, ctx, arena));
  if (ctrl == GateBit::kZero || ctrl == GateBit::kOne) return drive;
  GateBit passed = LowGateBit(EvalExpr(params.three_state_pass, ctx, arena));
  DriverStrength one_sided = drive;
  if (passed == GateBit::kZero) {
    one_sided.s1 = Strength::kHighz;
    return one_sided;
  }
  if (passed == GateBit::kOne) {
    one_sided.s0 = Strength::kHighz;
    return one_sided;
  }
  return drive;
}

static Net* DataInputNet(const Expr* data, SimContext& ctx) {
  const Expr* base = data->kind == ExprKind::kSelect ? data->base : data;
  if (base->kind == ExprKind::kMemberAccess) {
    return FindHierarchicalNet(base, ctx);
  }
  return base->kind == ExprKind::kIdentifier ? ctx.FindNet(base->text)
                                             : nullptr;
}

static NetStrength DataInputStrength(const Expr* data, SimContext& ctx) {
  Net* net = DataInputNet(data, ctx);
  if (net == nullptr) {
    return {Strength::kStrong, Strength::kStrong, Strength::kStrong,
            Strength::kStrong};
  }
  if (data->kind != ExprKind::kSelect) return net->resolved_strength;
  int64_t index = SelectBoundValue(EvalExpr(data->index, ctx, ctx.GetArena()));
  PackedRange range = net->resolved->DeclaredRange();
  return net->BitStrength(static_cast<uint32_t>(range.OffsetOf(index)));
}

static Strength ReducedRangeLow(Strength (*reduce)(Strength), Strength hi,
                                Strength lo) {
  Strength low = reduce(lo);
  return low == reduce(hi) ? Strength::kHighz : low;
}

static DriverStrength ComputeEffectiveDriverStrength(
    const ContAssignParams& params, SimContext& ctx) {
  DriverStrength effective_ds = params.ds;
  if (params.nonresistive_switch || params.resistive_switch) {
    NetStrength ns = DataInputStrength(params.data_input, ctx);
    auto reduce =
        params.resistive_switch ? &ReduceResistive : &ReduceNonresistive;
    effective_ds = {reduce(ns.s0_hi), reduce(ns.s1_hi),
                    ReducedRangeLow(reduce, ns.s0_hi, ns.s0_lo),
                    ReducedRangeLow(reduce, ns.s1_hi, ns.s1_lo)};
  }
  if (params.three_state_ctrl != nullptr &&
      params.three_state_pass != nullptr) {
    return ThreeStateGateStrength(params, effective_ds, ctx, ctx.GetArena());
  }
  return effective_ds;
}

static Logic4Vec EvalContAssignRhs(const ContAssignParams& params,
                                   SimContext& ctx, Arena& arena) {
  Logic4Vec value = EvalExpr(params.rhs, ctx, arena, params.width);
  if (params.rhs->kind != ExprKind::kStreamingConcat || params.width == 0)
    return value;
  return WidenStreamPackToFixedTarget(value, params.width,
                                      params.rhs->range.start, ctx, arena);
}

static bool ContAssignSupportsStructuredLhs(ExprKind k) {
  return k == ExprKind::kSelect || k == ExprKind::kConcatenation ||
         k == ExprKind::kAssignmentPattern || k == ExprKind::kStreamingConcat ||
         k == ExprKind::kMemberAccess;
}

static void ApplyContAssignToVariable(const ContAssignParams& params,
                                      const Logic4Vec& driven_val,
                                      SimContext& ctx, Arena& arena) {
  if (params.lhs->kind != ExprKind::kIdentifier) {
    PerformBlockingAssign(params.lhs, driven_val, ctx, arena);
    return;
  }
  if (params.rhs->kind == ExprKind::kConcatenation) {
    if (const ArrayInfo* info = ctx.FindArrayInfo(params.lhs->text)) {
      DistributeConcatToArray(params.lhs->text, *info, params.rhs, ctx, arena);
      return;
    }
  }
  auto* var = ctx.FindVariable(params.lhs->text);
  if (var == nullptr) return;
  if (!var->cont_assign_reevaluate) {
    var->cont_assign_reevaluate = [params, &ctx, &arena]() {
      ApplyContAssignToVariable(params, EvalContAssignRhs(params, ctx, arena),
                                ctx, arena);
    };
  }
  WriteVar(var, ConvertRealOnAssign(driven_val, params.lhs, *var, ctx, arena),
           arena);
}

static void ApplyContAssignResult(const ContAssignParams& params,
                                  const ContAssignDriver& drv,
                                  const ContAssignDrivenValue& driven,
                                  SimContext& ctx, Arena& arena) {
  if (drv.net) {
    ApplyContAssignToNet(drv, driven, &ctx.GetScheduler(), arena);
  } else {
    ApplyContAssignToVariable(params, driven.value, ctx, arena);
  }
}

static Logic4Vec CurrentContAssignOldValue(const ContAssignParams& params,
                                           const ContAssignDriver& drv,
                                           SimContext& ctx, Arena& arena) {
  if (drv.net != nullptr && !drv.first) {
    const Logic4Vec& own = drv.net->drivers[drv.driver_idx];
    return drv.partial ? ExtractBitField(arena, own, drv.lo, drv.width) : own;
  }
  Logic4Vec old_val = MakeLogic4VecVal(arena, 1, 0);
  auto* var = params.lhs->kind == ExprKind::kIdentifier
                  ? ctx.FindVariable(params.lhs->text)
                  : nullptr;
  if (var) {
    old_val = var->value;
  } else if (drv.net && drv.net->resolved) {
    old_val = drv.partial ? ExtractBitField(arena, drv.net->resolved->value,
                                            drv.lo, drv.width)
                          : drv.net->resolved->value;
  }
  return old_val;
}

static Logic4Vec ContAssignDrivenBits(const ContAssignDriver& drv,
                                      const Logic4Vec& val, Arena& arena) {
  if (!drv.partial || drv.width == 0) return val;
  return ExtractBitField(arena,
                         ResizeToWidth(val, drv.src_lo + drv.width, arena),
                         drv.src_lo, drv.width);
}

static uint32_t ContAssignTransitionWidth(const ContAssignDriver& drv,
                                          uint32_t declared_width) {
  return drv.partial ? drv.width : declared_width;
}

struct InertialReeval {
  bool collapsed = false;
  bool rescheduled = false;
  SimTime target;
};

struct PendingContAssignTransition {
  const Logic4Vec& old_val;
  Logic4Vec& val;
};

struct InertialLoopCtx {
  const ContAssignParams& params;
  const ContAssignDelays& d;
  const ContAssignDriver& drv;
  SimContext& ctx;
  Arena& arena;
};

static InertialReeval ReevalInertialContAssign(
    const InertialLoopCtx& loop, const PendingContAssignTransition& xition) {
  InertialReeval result;
  auto new_val = EvalContAssignRhs(loop.params, loop.ctx, loop.arena);
  if (Logic4VecEqual(new_val, xition.val)) return result;
  xition.val = new_val;
  auto driven = ContAssignDrivenBits(loop.drv, new_val, loop.arena);
  if (Logic4VecEqual(driven, xition.old_val)) {
    result.collapsed = true;
    return result;
  }
  uint64_t ticks = SelectTransitionDelay(
      loop.params.whole,
      {xition.old_val, driven,
       ContAssignTransitionWidth(loop.drv, loop.params.width)},
      loop.d, loop.ctx, loop.arena);
  result.rescheduled = true;
  result.target = loop.ctx.CurrentTime() + SimTime{ticks};
  return result;
}

static void CommitContAssignValue(const ContAssignParams& params,
                                  const ContAssignDriver& drv,
                                  const Logic4Vec& val, SimContext& ctx,
                                  Arena& arena) {
  DriverStrength effective_ds = ComputeEffectiveDriverStrength(params, ctx);
  auto driven_val = ApplyHighzStrengthsToValue(val, effective_ds, arena);
  ApplyContAssignResult(
      params, drv, ContAssignDrivenValue{driven_val, effective_ds}, ctx, arena);
}

static Net* NetNamedBy(const Expr* e, SimContext& ctx) {
  if (e->kind == ExprKind::kIdentifier) return ctx.FindNet(e->text);
  if (e->kind != ExprKind::kMemberAccess) return nullptr;
  return FindHierarchicalNet(e, ctx);
}

static Net* NetArrayElementNamedBy(const Expr* e, SimContext& ctx) {
  if (e->kind != ExprKind::kSelect || e->index_end != nullptr ||
      e->base == nullptr || e->base->kind != ExprKind::kIdentifier ||
      e->index == nullptr) {
    return nullptr;
  }
  std::string_view name = e->base->text;
  if (ctx.FindArrayInfo(name) == nullptr || ctx.FindNet(name) == nullptr) {
    return nullptr;
  }
  Logic4Vec idx = EvalExpr(e->index, ctx, ctx.GetArena());
  if (!idx.IsKnown()) return nullptr;
  return ctx.FindNet(std::string(name) + "[" + std::to_string(idx.ToUint64()) +
                     "]");
}

static ContAssignDriver MakeContAssignDriver(const Expr* lhs, SimContext& ctx) {
  ContAssignDriver drv;
  if (lhs->kind == ExprKind::kIdentifier ||
      lhs->kind == ExprKind::kMemberAccess) {
    drv.net = NetNamedBy(lhs, ctx);
  } else if (Net* elem = NetArrayElementNamedBy(lhs, ctx)) {
    drv.net = elem;
  } else if (lhs->kind == ExprKind::kSelect && lhs->base != nullptr) {
    Net* net = NetNamedBy(lhs->base, ctx);
    if (net == nullptr) net = NetArrayElementNamedBy(lhs->base, ctx);
    if (net != nullptr && net->resolved != nullptr) {
      drv.net = net;
      drv.partial = true;
    }
  }
  drv.driver_idx = drv.net ? drv.net->drivers.size() : 0;
  drv.first = true;
  if (const Process* proc = ctx.CurrentProcess())
    drv.origin = proc->inst_prefix;
  return drv;
}

static void RefreshContAssignDriverBits(ContAssignDriver& drv, const Expr* lhs,
                                        SimContext& ctx, Arena& arena) {
  if (!drv.partial || drv.net == nullptr) return;
  PartSelectBits bits = SelectStorageBits(*drv.net->resolved, lhs, ctx, arena);
  drv.lo = bits.lo;
  drv.width = bits.width;
  drv.src_lo = bits.src_lo;
}

static uint64_t RemainingTicks(SimTime target, SimContext& ctx) {
  return (target.ticks > ctx.CurrentTime().ticks)
             ? (target.ticks - ctx.CurrentTime().ticks)
             : 0;
}

static bool ApplyInertialReeval(const InertialLoopCtx& loop,
                                const PendingContAssignTransition& xition,
                                SimTime& target) {
  InertialReeval re = ReevalInertialContAssign(loop, xition);
  if (re.collapsed) return true;
  if (re.rescheduled) target = re.target;
  return false;
}

static ExecTask RunInertialContAssignDelay(
    const InertialLoopCtx& loop, const std::vector<std::string_view>& read_vars,
    const Logic4Vec& old_val, Logic4Vec& val, uint64_t ticks) {
  SimTime target = loop.ctx.CurrentTime() + SimTime{ticks};
  for (uint64_t remaining = RemainingTicks(target, loop.ctx); remaining > 0;
       remaining = RemainingTicks(target, loop.ctx)) {
    if (co_await InertialDelayAwaiter{loop.ctx, remaining, read_vars}) break;
    if (ApplyInertialReeval(loop, PendingContAssignTransition{old_val, val},
                            target))
      break;
  }
  co_return StmtResult::kDone;
}

static std::string_view ContAssignTargetName(const Expr* lhs) {
  if (lhs == nullptr) return {};
  if (lhs->kind == ExprKind::kIdentifier) return lhs->text;
  if (lhs->kind == ExprKind::kSelect && lhs->base != nullptr &&
      lhs->base->kind == ExprKind::kIdentifier) {
    return lhs->base->text;
  }
  return {};
}

static const SpecifyManager* ModulePathManagerFor(SimContext& ctx,
                                                  std::string_view target) {
  if (target.empty()) return nullptr;
  const SpecifyManager* mgr = ctx.GetSpecifyManager();
  if (mgr == nullptr) return nullptr;
  if (!IsModulePathOutput(*mgr, target)) return nullptr;
  return mgr;
}

struct ContAssignWait {
  const ContAssignParams& params;
  SimContext& ctx;
  Arena& arena;
  const std::vector<std::string_view>& read_vars;
  const SpecifyManager* path_mgr;
  std::string_view path_output;
  const std::function<void(const Logic4Vec&)>& commit;
};

static bool AnnotatedGateDelays(const ContAssignParams& params, SimContext& ctx,
                                ContAssignDelays& d) {
  const SpecifyManager* mgr = ctx.GetSpecifyManager();
  if (mgr == nullptr) return false;
  const PrimitiveDriver* driver = mgr->FindAnnotatedPrimitiveDriver(
      params.inst_prefix, ContAssignTargetName(params.lhs));
  if (driver == nullptr) return false;
  d.rise = driver->delays[0];
  d.fall = driver->delays[1];
  d.decay = driver->delays[2];
  d.has_fall = true;
  d.has_decay = true;
  return true;
}

static ExecTask RunContAssignWait(const ContAssignWait& w,
                                  const ContAssignDriver& drv, Logic4Vec& val,
                                  bool* committed) {
  ContAssignDelays d;
  bool delayed = w.params.delays.rise != nullptr;
  if (delayed) d = BuildContAssignDelays(w.params.delays, w.ctx, w.arena);
  if (AnnotatedGateDelays(w.params, w.ctx, d)) delayed = true;
  Logic4Vec old_val = CurrentContAssignOldValue(w.params, drv, w.ctx, w.arena);
  Logic4Vec driven = ContAssignDrivenBits(drv, val, w.arena);
  uint64_t ticks = delayed
                       ? SelectTransitionDelay(
                             w.params.whole,
                             {old_val, driven,
                              ContAssignTransitionWidth(drv, w.params.width)},
                             d, w.ctx, w.arena)
                       : 0;

  const bool kFirstAtPort = !w.params.module_path_port.empty() && drv.first;
  if (kFirstAtPort && w.path_mgr != nullptr &&
      !ModulePathSourcesOf(*w.path_mgr, w.path_output).empty()) {
    val = MakeAllX(w.arena, val.width);
  }
  if (w.path_mgr != nullptr && !kFirstAtPort &&
      !Logic4VecEqual(driven, old_val)) {
    const bool kAtPort = !w.params.module_path_port.empty();
    std::vector<std::string> path_sources;
    std::vector<std::string_view> wake = w.read_vars;
    if (kAtPort) {
      path_sources = ModulePathSourcesOf(*w.path_mgr, w.path_output);
      wake.insert(wake.end(), path_sources.begin(), path_sources.end());
    }
    ModulePathDrive drive{w.ctx,    w.arena,      *w.path_mgr,    w.path_output,
                          wake,     w.params.rhs, w.params.width, ticks,
                          w.commit, kAtPort};
    co_await RunModulePathTransition(drive, old_val, val, committed);
    co_return StmtResult::kDone;
  }

  if (ticks > 0 && !w.read_vars.empty()) {
    InertialLoopCtx loop{w.params, d, drv, w.ctx, w.arena};
    co_await RunInertialContAssignDelay(loop, w.read_vars, old_val, val, ticks);
  } else if (ticks > 0) {
    co_await DelayAwaiter{w.ctx, ticks};
  }
  co_return StmtResult::kDone;
}

struct InterconnectDelayQuery {
  const ContAssignParams& params;
  const ContAssignDriver& drv;
  const Logic4Vec& val;
  SimContext& ctx;
  Arena& arena;
};

static void CommitAcrossInterconnect(
    const InterconnectDelayQuery& q,
    const std::shared_ptr<InterconnectSchedule>& schedule,
    const std::function<void(const Logic4Vec&)>& commit) {
  const SpecifyManager* mgr = q.ctx.GetSpecifyManager();
  if (schedule->shadow != nullptr && mgr != nullptr &&
      mgr->HasSourceSpecificInterconnectDelay(q.params.interconnect_load)) {
    return;
  }
  const std::optional<InterconnectDelay> kAnnotated =
      q.params.interconnect_load.empty() || mgr == nullptr
          ? std::nullopt
          : mgr->ConnectionInterconnectDelay(q.params.interconnect_source,
                                             q.params.interconnect_load);
  if (!kAnnotated.has_value() && schedule->pending.empty()) {
    commit(q.val);
    return;
  }
  const Logic4Vec kHeld =
      CurrentContAssignOldValue(q.params, q.drv, q.ctx, q.arena);
  const Logic4Vec kBits = ContAssignDrivenBits(q.drv, q.val, q.arena);
  DriveAcrossInterconnect(schedule, kAnnotated.value_or(InterconnectDelay{}),
                          InterconnectChange{kHeld, q.val, kBits}, q.ctx,
                          commit);
}

static void FollowConnectedNet(
    const ContAssignParams& params, InterconnectSchedule& schedule,
    SimContext& ctx, const std::function<void(const Logic4Vec&)>& commit) {
  if (params.interconnect_source.empty()) return;
  std::string dotted = params.interconnect_source;
  std::ranges::replace(dotted, '/', '.');
  Net* net = ctx.FindNet(dotted);
  if (net == nullptr) return;
  schedule.shadow = std::make_shared<InterconnectShadow>();
  FollowNetDrivers(
      *net, schedule.shadow,
      InterconnectEnds{params.interconnect_source, params.interconnect_load},
      ctx, commit);
}

static std::string ModulePathOutputName(const ContAssignParams& params) {
  if (!params.module_path_port.empty()) return params.module_path_port;
  if (params.path_delayed_at_connection) return {};
  std::string_view target_name = ContAssignTargetName(params.lhs);
  if (target_name.empty()) return {};
  return params.inst_prefix + std::string(target_name);
}

static bool WatchDataInputStrength(const ContAssignParams& params,
                                   SimContext& ctx) {
  if (!params.nonresistive_switch && !params.resistive_switch) return false;
  Net* net = DataInputNet(params.data_input, ctx);
  if (net != nullptr) net->strength_watched = true;
  return true;
}

static SimCoroutine MakeContAssignCoroutine(ContAssignParams params,
                                            SimContext& ctx, Arena& arena) {
  if (!params.lhs) co_return;
  bool lhs_is_name = params.lhs->kind == ExprKind::kIdentifier;
  if (!lhs_is_name && !ContAssignSupportsStructuredLhs(params.lhs->kind)) {
    co_return;
  }

  std::unordered_set<std::string> read_strs;
  CollectExprAndStaticReads(params.rhs, ctx, read_strs);
  std::vector<std::string_view> read_vars(read_strs.begin(), read_strs.end());
  DropUnwatchableNames(ctx, read_vars);
  bool passes_strength = WatchDataInputStrength(params, ctx);

  ContAssignDriver drv = MakeContAssignDriver(params.lhs, ctx);
  if (params.preset_driver >= 0 && drv.net != nullptr) {
    drv.driver_idx = static_cast<size_t>(params.preset_driver);
    drv.first = false;
  }

  std::string path_output = ModulePathOutputName(params);

  std::function<void(const Logic4Vec&)> commit = [&](const Logic4Vec& v) {
    CommitContAssignValue(params, drv, v, ctx, arena);
    drv.first = false;
  };
  InterconnectScheduleOwner interconnect;
  FollowConnectedNet(params, *interconnect.schedule, ctx, commit);
  drv.source_port = params.module_path_port;

  const SpecifyManager* path_mgr = ModulePathManagerFor(ctx, path_output);

  bool evaluated_once = false;
  while (!evaluated_once || !ctx.StopRequested()) {
    evaluated_once = true;
    auto val = EvalContAssignRhs(params, ctx, arena);
    RefreshContAssignDriverBits(drv, params.lhs, ctx, arena);

    bool committed = false;
    if (ContAssignDelays filed; params.delays.rise || path_mgr != nullptr ||
                                AnnotatedGateDelays(params, ctx, filed)) {
      ContAssignWait wait{params,   ctx,         arena, read_vars,
                          path_mgr, path_output, commit};
      co_await RunContAssignWait(wait, drv, val, &committed);
    }

    if (!committed) {
      InterconnectDelayQuery query{params, drv, val, ctx, arena};
      CommitAcrossInterconnect(query, interconnect.schedule, commit);
    }

    if (read_vars.empty()) {
      co_await AwaitInterconnectArrivals(*interconnect.schedule, ctx);
      break;
    }
    co_await AnyChangeAwaiter{ctx, read_vars, nullptr, passes_strength};
  }
}
static int64_t PresetDelayedDriver(const ContAssignParams& p, SimContext& ctx,
                                   Arena& arena) {
  if (p.delays.rise == nullptr) return -1;
  ContAssignDriver drv = MakeContAssignDriver(p.lhs, ctx);
  if (drv.net == nullptr || drv.net->resolved == nullptr) return -1;
  RefreshContAssignDriverBits(drv, p.lhs, ctx, arena);
  auto slot = static_cast<int64_t>(drv.net->drivers.size());
  drv.net->drivers.push_back(ContAssignDriverValue(
      drv, MakeAllX(arena, drv.net->resolved->value.width), arena));
  drv.net->driver_strengths.push_back(p.ds);
  drv.net->Resolve(arena, nullptr);
  return slot;
}

void Lowerer::LowerContAssign(const RtlirContAssign& ca, bool from_program) {
  auto* p = arena_.Create<Process>();
  p->kind = ProcessKind::kContAssign;
  p->id = next_id_++;

  p->home_region = from_program
                       ? Scheduler::HomeRegionForReactiveBlockingAssign()
                       : Region::kActive;
  p->is_reactive = from_program;

  p->inst_prefix = inst_prefix_;
  p->gen_prefixes.assign(ca.gen_block_prefixes.begin(),
                         ca.gen_block_prefixes.end());
  InstallGenBlockConsts(ca.gen_block_consts, p);
  ContAssignParams cap;
  cap.lhs = ca.lhs;
  cap.rhs = ca.rhs;
  cap.ds = {StrengthFromParserCode(ca.drive_strength0),
            StrengthFromParserCode(ca.drive_strength1)};
  cap.nonresistive_switch = ca.from_nonresistive_switch;
  cap.resistive_switch = ca.from_resistive_switch;
  cap.data_input = ca.data_input;
  cap.three_state_ctrl = ca.three_state_ctrl;
  cap.three_state_pass = ca.three_state_pass;
  cap.delays = {ca.delay, ca.delay_fall, ca.delay_decay};
  cap.width = ca.width;
  cap.whole = WholeOfConcatElement(ca);
  cap.inst_prefix = inst_prefix_;
  cap.interconnect_load = ca.interconnect_load;
  cap.interconnect_source = ca.interconnect_source;
  cap.preset_driver = PresetDelayedDriver(cap, ctx_, arena_);
  cap.module_path_port = ca.module_path_port;
  cap.path_delayed_at_connection = path_delayed_ports_.contains(
      inst_prefix_ + std::string(ContAssignTargetName(ca.lhs)));
  p->coro = MakeContAssignCoroutine(cap, ctx_, arena_).Release();

  ScheduleProcess(p, ctx_);
}
}  // namespace delta
