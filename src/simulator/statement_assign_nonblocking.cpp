#include <cstdint>
#include <functional>
#include <limits>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/class_gc_roots.h"
#include "simulator/class_object.h"
#include "simulator/clocking.h"
#include "simulator/eval_array.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_args_internal.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/modport_expression.h"
#include "simulator/queue_bound.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"

namespace delta {

struct NbaWrite {
  Event* event;
  Variable* var;
  const Logic4Vec& rhs_val;
  Arena& arena;
};

struct NbaScheduleSlot {
  SimTime time;
  Region region;
  SimContext& ctx;
  Arena& arena;
};

static void SetupWholeVarNbaCallback(Event* event, Variable* var,
                                     const Logic4Vec& rhs_val);

static void ScheduleNbaEvent(Event* event, uint64_t delay_ticks,
                             SimContext& ctx) {
  auto region = ctx.IsReactiveContext() ? Region::kReNBA : Region::kNBA;
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime() + SimTime{delay_ticks},
                                   region, event);
}

static Logic4Vec SampleNbaRhs(const Logic4Vec& val, Arena& arena) {
  Logic4Vec copy = ExtractBitField(arena, val, 0, val.width);
  copy.is_real = val.is_real;
  copy.is_signed = val.is_signed;
  copy.is_string = val.is_string;
  return copy;
}

static void SampleConcatElements(std::vector<Logic4Vec>& elems, Arena& arena) {
  for (auto& elem : elems) elem = SampleNbaRhs(elem, arena);
}

static void ScheduleArrayConcatNbaElements(const Stmt* stmt,
                                           const ArrayInfo* ainfo,
                                           const std::vector<Logic4Vec>& elems,
                                           const NbaScheduleSlot& slot) {
  uint32_t count = ArrayElementCount(*ainfo);
  if (elems.size() != count) {
    slot.ctx.GetDiag().Error(
        stmt->range.start,
        "unpacked array concatenation size mismatch: expected " +
            std::to_string(count) + " elements, got " +
            std::to_string(elems.size()),
        Subclause("10.10"));
    return;
  }
  for (uint32_t i = 0; i < count; ++i) {
    auto name = std::string(stmt->lhs->text) + ArrayElementSuffixAt(*ainfo, i);
    auto* var = slot.ctx.FindVariable(name);
    if (!var) continue;
    auto val = ResizeToWidth(elems[i], ainfo->elem_width, slot.arena);
    auto* event = slot.ctx.GetScheduler().GetEventPool().Acquire();
    SetupWholeVarNbaCallback(event, var, val);
    PinEventHandles(*event, slot.ctx, {val});
    slot.ctx.GetScheduler().ScheduleEvent(slot.time, slot.region, event);
  }
}

static bool IsQueueValuedRhs(const Expr* rhs, SimContext& ctx) {
  if (rhs->kind == ExprKind::kConcatenation) return true;
  if (rhs->kind != ExprKind::kSelect || !rhs->base || !rhs->index_end)
    return false;
  return rhs->base->kind == ExprKind::kIdentifier &&
         ctx.FindQueue(rhs->base->text) != nullptr;
}

static bool UpdateTimeReachable(uint64_t delay_ticks, const SimContext& ctx) {
  return delay_ticks <=
         std::numeric_limits<uint64_t>::max() - ctx.CurrentTime().ticks;
}

static uint64_t IntraAssignDelayTicks(const Stmt* stmt, SimContext& ctx,
                                      Arena& arena) {
  if (!stmt->delay) return 0;
  return DelayExprToTicks(stmt->delay, ctx, arena);
}

static std::vector<Logic4Vec> SampleConcatNbaElements(const Stmt* stmt,
                                                      bool fixed_target,
                                                      SimContext& ctx,
                                                      Arena& arena) {
  std::vector<Logic4Vec> elems;
  if (fixed_target) {
    elems = CollectConcatElements(stmt->rhs, ctx, arena);
  } else {
    CollectQueueElements(stmt->rhs, ctx, arena, elems);
  }
  SampleConcatElements(elems, arena);
  return elems;
}

static void ScheduleQueueConcatNba(QueueObject* q, const Stmt* stmt,
                                   std::vector<Logic4Vec> elems,
                                   const NbaScheduleSlot& slot) {
  SimContext& ctx = slot.ctx;
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->kind = EventKind::kUpdate;
  const std::vector<Logic4Vec> kCarried = elems;
  event->callback = [q, &ctx, loc = stmt->rhs->range.start,
                     elems = std::move(elems)]() {
    q->elements = elems;
    EnforceQueueBound(q, "nonblocking assignment", loc, ctx);
    q->AssignFreshIds();
    ++q->generation;
  };
  PinEventHandles(*event, ctx, kCarried);
  ctx.GetScheduler().ScheduleEvent(slot.time, slot.region, event);
}

static bool TryArrayConcatNba(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier || !stmt->rhs)
    return false;

  auto* ainfo = ctx.FindArrayInfo(stmt->lhs->text);
  if (ainfo != nullptr && ainfo->is_dynamic) ainfo = nullptr;
  auto* q = ainfo ? nullptr : ctx.FindQueue(stmt->lhs->text);
  if (!ainfo && !q) return false;
  if (ainfo && stmt->rhs->kind != ExprKind::kConcatenation) return false;
  if (q && !IsQueueValuedRhs(stmt->rhs, ctx)) return false;

  std::vector<Logic4Vec> elems =
      SampleConcatNbaElements(stmt, ainfo != nullptr, ctx, arena);
  const uint64_t kDelay = IntraAssignDelayTicks(stmt, ctx, arena);
  if (!UpdateTimeReachable(kDelay, ctx)) return true;
  auto nba_region = ctx.IsReactiveContext() ? Region::kReNBA : Region::kNBA;
  NbaScheduleSlot slot{ctx.CurrentTime() + SimTime{kDelay}, nba_region, ctx,
                       arena};

  if (ainfo) {
    ScheduleArrayConcatNbaElements(stmt, ainfo, elems, slot);
  } else {
    ScheduleQueueConcatNba(q, stmt, std::move(elems), slot);
  }
  return true;
}

static bool TaggedUnionTargetKey(const Expr* lhs, SimContext& ctx,
                                 std::string& key) {
  if (lhs == nullptr) return false;
  if (lhs->kind == ExprKind::kMemberAccess)
    return TaggedUnionMemberKey(lhs, ctx, key);
  if (lhs->kind != ExprKind::kIdentifier) return false;
  const StructTypeInfo* layout = StructLayoutOfName(lhs->text, ctx);
  if (layout == nullptr || !layout->is_union) return false;
  key = TagKeyOfName(lhs->text, ctx);
  return true;
}

static Logic4Vec EvalNbaRhs(const Stmt* stmt, SimContext& ctx, Arena& arena,
                            NbaUpdateTag& update) {
  update = NbaUpdateTag{};
  std::string key;
  if (stmt->rhs == nullptr || !TaggedUnionTargetKey(stmt->lhs, ctx, key))
    return EvalRhsWithStructContext(stmt, ctx, arena);
  std::string tag;
  Logic4Vec value = stmt->rhs->kind == ExprKind::kCall
                        ? EvalWithReturnedTag(stmt->rhs, ctx, arena, tag)
                        : EvalRhsWithStructContext(stmt, ctx, arena);
  if (stmt->rhs->kind == ExprKind::kTagged && stmt->rhs->rhs != nullptr)
    tag = std::string(stmt->rhs->rhs->text);
  if (tag.empty()) return value;
  update = NbaUpdateTag{*arena.Create<std::string>(key),
                        *arena.Create<std::string>(tag)};
  return value;
}

NbaSample SampleNonblockingRhs(const Stmt* stmt, SimContext& ctx,
                               Arena& arena) {
  NbaSample sample;
  sample.value = EvalNbaRhs(stmt, ctx, arena, sample.tag);
  sample.value =
      ApplyStreamPackToTargetWidening(stmt, sample.value, ctx, arena);
  sample.value = SampleNbaRhs(sample.value, arena);
  return sample;
}

static void AttachUpdateTag(Event* event, const Variable* forced_var,
                            const NbaUpdateTag& update, SimContext& ctx) {
  if (!update.Carries()) return;
  std::function<void()> deposit = std::move(event->callback);
  event->callback = [deposit, forced_var, update, &ctx]() {
    deposit();
    if (forced_var == nullptr || !forced_var->is_forced)
      ctx.SetVariableTag(update.key, update.tag);
  };
}

StmtResult ExecNonblockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  if (TryArrayConcatNba(stmt, ctx, arena)) return StmtResult::kDone;

  NbaSample sample = SampleNonblockingRhs(stmt, ctx, arena);
  const uint64_t kDelay = IntraAssignDelayTicks(stmt, ctx, arena);
  if (!UpdateTimeReachable(kDelay, ctx)) return StmtResult::kDone;
  ScheduleNonblockingAssign(stmt, sample, kDelay, ctx, arena);
  return StmtResult::kDone;
}

static void SetupWholeVarNbaCallback(Event* event, Variable* var,
                                     const Logic4Vec& rhs_val) {
  event->kind = EventKind::kUpdate;
  var->pending_nba = rhs_val;
  var->has_pending_nba = true;
  event->callback = [var, rhs_val]() {
    if (!var->is_forced) {
      var->value = rhs_val;
      if (!var->is_4state) CoerceTo2State(var->value);
      var->NotifyWatchers();
    }
    var->has_pending_nba = false;
  };
}

namespace {
using LhsWriter = void (*)(const Expr*, const Logic4Vec&, SimContext&, Arena&);
struct DeferredLhsWrite {
  const Expr* lhs;
  Logic4Vec value;
  LhsWriter write;
};
}  // namespace

static void ScheduleDeferredLhsWrite(const DeferredLhsWrite& w,
                                     uint64_t delay_ticks, SimContext& ctx,
                                     Arena& arena) {
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->kind = EventKind::kUpdate;
  auto snaps = CollectLhsIndexSnapshots(w.lhs, ctx, arena);
  event->callback = [w, snaps, &ctx, &arena]() {
    InstallLhsIndexSnapshots(snaps, ctx);
    w.write(w.lhs, w.value, ctx, arena);
    ClearLhsIndexSnapshots(snaps, ctx);
  };
  PinEventHandles(*event, ctx, {w.value});
  ScheduleNbaEvent(event, delay_ticks, ctx);
}

static void ScheduleStreamingConcatNba(const Stmt* stmt,
                                       const Logic4Vec& rhs_val,
                                       uint64_t delay_ticks, SimContext& ctx,
                                       Arena& arena) {
  ScheduleDeferredLhsWrite({stmt->lhs, rhs_val, UnpackStreamingConcatLhs},
                           delay_ticks, ctx, arena);
}

static bool NamesSelectedElementMember(const Expr* el) {
  return el->kind == ExprKind::kMemberAccess && el->lhs != nullptr &&
         el->lhs->kind == ExprKind::kSelect;
}

static void ScheduleConcatNba(const Stmt* stmt, const Logic4Vec& rhs_val,
                              uint64_t delay_ticks, SimContext& ctx,
                              Arena& arena) {
  const Expr* lhs = UnwrapTypedPattern(stmt->lhs);
  uint32_t bit_offset = 0;
  for (auto it = lhs->elements.rbegin(); it != lhs->elements.rend(); ++it) {
    Expr* el = *it;
    uint32_t width = ConcatLhsElemWidth(el, ctx, arena);
    if (width == 0) {
      ReportZeroWidthPartSelect(el, ctx, arena);
      continue;
    }
    NbaSample part;
    part.value = ExtractBitField(arena, rhs_val, bit_offset, width);
    bit_offset += width;
    if (NamesSelectedElementMember(el)) {
      ScheduleDeferredLhsWrite({el, part.value, PerformBlockingAssign},
                               delay_ticks, ctx, arena);
      continue;
    }
    auto* el_stmt = arena.Create<Stmt>(*stmt);
    el_stmt->lhs = el;
    ScheduleNonblockingAssign(el_stmt, part, delay_ticks, ctx, arena);
  }
}

static void SetupPartSelectNbaCallback(const NbaWrite& write,
                                       const PartSelectBits& bits) {
  Variable* var = write.var;
  Logic4Vec rhs_val = write.rhs_val;
  Arena& arena = write.arena;
  write.event->callback = [var, bits, rhs_val, &arena]() {
    if (var->is_forced) return;
    WritePartSelect(var, bits, rhs_val, arena);
    var->NotifyWatchers();
  };
}

static bool SetupSelectNbaCallback(const NbaWrite& write, const Expr* lhs,
                                   SimContext& ctx) {
  PartSelectBits bits = SelectStorageBits(*write.var, lhs, ctx, write.arena);
  if (bits.width == 0) return false;
  SetupPartSelectNbaCallback(write, bits);
  return true;
}

static Variable* ResolveNbaSelectElement(const Expr* lhs, SimContext& ctx,
                                         Arena& arena, bool* absent_element) {
  *absent_element = false;
  if (lhs->kind != ExprKind::kSelect) return nullptr;
  if (auto* elem = TryResolveArrayElement(lhs, ctx)) return elem;
  if (TryResolveCompoundElementBase(lhs, ctx, arena) != nullptr) return nullptr;
  return TryResolveCompoundElement(lhs, ctx, arena, absent_element);
}

static const ClockingSignal* FindClockvarSignal(const Expr* lhs,
                                                SimContext& ctx,
                                                std::string_view* block_name) {
  if (lhs->kind != ExprKind::kMemberAccess || lhs->lhs == nullptr) {
    return nullptr;
  }
  const ClockingBlock* block = ResolveClockingBlockOf(lhs->lhs, ctx);
  if (block == nullptr) return nullptr;
  std::string_view member = lhs->text;
  if (lhs->rhs != nullptr && lhs->rhs->kind == ExprKind::kIdentifier) {
    member = lhs->rhs->text;
  }
  if (member.empty()) return nullptr;
  for (const auto& sig : block->signals) {
    if (sig.signal_name != member) continue;
    if (sig.direction == ClockingDir::kInput) return nullptr;
    *block_name = block->name;
    return &sig;
  }
  return nullptr;
}

static bool TryScheduleClockvarDrive(const Expr* lhs, const Logic4Vec& rhs_val,
                                     SimContext& ctx, uint32_t cycles = 0) {
  std::string_view block_name;
  const ClockingSignal* sig = FindClockvarSignal(lhs, ctx, &block_name);
  if (sig == nullptr) return false;
  ctx.GetClockingManager()->ScheduleCycleDelayedDrive(
      ClockvarDrive{block_name, sig->signal_name, ClockingValue::Of(rhs_val),
                    cycles},
      ctx, ctx.GetScheduler());
  return true;
}

static Expr* IndexLiteral(const Expr* like, const Logic4Vec& v, Arena& arena) {
  auto* literal = arena.Create<Expr>();
  literal->kind = ExprKind::kIntegerLiteral;
  literal->range = like->range;
  std::string text = std::to_string(v.ToUint64());
  literal->text = {arena.AllocString(text.data(), text.size()), text.size()};
  literal->int_val = v.ToUint64();
  return literal;
}

static bool TryScheduleClockvarSelectDrive(const Expr* lhs,
                                           const Logic4Vec& rhs_val,
                                           uint32_t cycles, SimContext& ctx,
                                           Arena& arena) {
  if (lhs->kind != ExprKind::kSelect || lhs->base == nullptr ||
      lhs->base->kind != ExprKind::kMemberAccess || lhs->index == nullptr) {
    return false;
  }
  std::string_view block_name;
  const ClockingSignal* sig = FindClockvarSignal(lhs->base, ctx, &block_name);
  if (sig == nullptr || sig->target_expr != nullptr) return false;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->range = lhs->base->range;
  base->text = sig->target_path.empty() ? sig->signal_name : sig->target_path;
  auto* target = arena.Create<Expr>(*lhs);
  target->base = base;
  target->index =
      IndexLiteral(lhs->index, EvalExpr(lhs->index, ctx, arena), arena);
  if (lhs->index_end != nullptr) {
    target->index_end = IndexLiteral(
        lhs->index_end, EvalExpr(lhs->index_end, ctx, arena), arena);
  }
  ctx.GetClockingManager()->ScheduleCycleDelayedDrive(
      ClockvarDrive{block_name, sig->signal_name, ClockingValue::Of(rhs_val),
                    cycles, target},
      ctx, ctx.GetScheduler());
  return true;
}

static bool TryScheduleSynchronousDrive(const Stmt* stmt,
                                        const Logic4Vec& rhs_val,
                                        SimContext& ctx, Arena& arena) {
  uint32_t cycles =
      stmt->cycle_delay != nullptr
          ? static_cast<uint32_t>(
                EvalExpr(stmt->cycle_delay, ctx, arena).ToUint64())
          : 0;
  if (stmt->cycle_delay != nullptr &&
      stmt->lhs->kind == ExprKind::kMemberAccess &&
      TryScheduleClockvarDrive(stmt->lhs, rhs_val, ctx, cycles)) {
    return true;
  }
  return TryScheduleClockvarSelectDrive(stmt->lhs, rhs_val, cycles, ctx, arena);
}

static void ScheduleResolvedFieldNba(const FieldTarget& target,
                                     const NbaSample& sample,
                                     uint64_t delay_ticks, SimContext& ctx,
                                     Arena& arena);

static void ScheduleFieldNba(const Expr* lhs, const NbaSample& sample,
                             uint64_t delay_ticks, SimContext& ctx,
                             Arena& arena) {
  if (lhs->kind == ExprKind::kIdentifier) {
    ScheduleResolvedFieldNba(ResolveBarePropertyTarget(lhs->text, ctx), sample,
                             delay_ticks, ctx, arena);
    return;
  }
  if (lhs->kind != ExprKind::kMemberAccess) return;
  if (TryScheduleClockvarDrive(lhs, sample.value, ctx)) return;
  ScheduleResolvedFieldNba(ResolveFieldTarget(lhs, ctx), sample, delay_ticks,
                           ctx, arena);
}

static void ScheduleResolvedFieldNba(const FieldTarget& target,
                                     const NbaSample& sample,
                                     uint64_t delay_ticks, SimContext& ctx,
                                     Arena& arena) {
  if (!target.HasDeposit()) return;
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->kind = EventKind::kUpdate;
  event->callback = [target, value = sample.value, &ctx, &arena]() {
    WriteResolvedField(target, value, ctx, arena);
  };
  PinEventHandles(*event, ctx, {sample.value}, target.obj);
  AttachUpdateTag(event, nullptr, sample.tag, ctx);
  ScheduleNbaEvent(event, delay_ticks, ctx);
}

static bool TryScheduleElsewhere(const Stmt* stmt, const NbaSample& sample,
                                 uint64_t delay_ticks, SimContext& ctx,
                                 Arena& arena) {
  return TryModportExpressionNonblocking(stmt, sample, delay_ticks, ctx,
                                         arena) ||
         TryScheduleSynchronousDrive(stmt, sample.value, ctx, arena);
}

void ScheduleNonblockingAssign(const Stmt* stmt, const NbaSample& sample,
                               uint64_t delay_ticks, SimContext& ctx,
                               Arena& arena) {
  if (!stmt->lhs) return;
  LhsIndexPin pin(stmt->lhs, ctx, arena);

  const Logic4Vec& rhs_val = sample.value;
  if (TryScheduleElsewhere(stmt, sample, delay_ticks, ctx, arena)) return;
  if (stmt->lhs->kind == ExprKind::kStreamingConcat) {
    ScheduleStreamingConcatNba(stmt, rhs_val, delay_ticks, ctx, arena);
    return;
  }
  if (IsConcatLhs(stmt->lhs)) {
    ScheduleConcatNba(stmt, rhs_val, delay_ticks, ctx, arena);
    return;
  }

  bool is_select = (stmt->lhs->kind == ExprKind::kSelect);
  bool absent_element = false;
  auto* elem = ResolveNbaSelectElement(stmt->lhs, ctx, arena, &absent_element);
  if (absent_element) return;
  auto* sub_elem =
      elem ? nullptr : TryResolveCompoundElementBase(stmt->lhs, ctx, arena);
  auto* var = elem                  ? elem
              : sub_elem != nullptr ? sub_elem
                                    : ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) {
    ScheduleFieldNba(stmt->lhs, sample, delay_ticks, ctx, arena);
    return;
  }

  auto* event = ctx.GetScheduler().GetEventPool().Acquire();

  event->kind = EventKind::kUpdate;
  if (is_select && !elem) {
    NbaWrite write{event, var, rhs_val, arena};
    if (!SetupSelectNbaCallback(write, stmt->lhs, ctx)) {
      ctx.GetScheduler().GetEventPool().Release(event);
      return;
    }
  } else {
    auto converted = ConvertRealOnAssign(rhs_val, stmt->lhs, *var, ctx, arena);
    SetupWholeVarNbaCallback(event, var, converted);
    AttachUpdateTag(event, var, sample.tag, ctx);
  }
  PinEventHandles(*event, ctx, {rhs_val});
  ScheduleNbaEvent(event, delay_ticks, ctx);
}

Scheduler::NbaCapture* CaptureNonblockingAssign(const Stmt* stmt,
                                                const NbaSample& sample,
                                                SimContext& ctx, Arena& arena) {
  auto* updates = arena.Create<Scheduler::NbaCapture>();
  ctx.GetScheduler().SetNbaCapture(updates);
  ScheduleNonblockingAssign(stmt, sample, 0, ctx, arena);
  ctx.GetScheduler().SetNbaCapture(nullptr);
  return updates;
}

void ReleaseNbaUpdates(const Scheduler::NbaCapture& updates, SimContext& ctx) {
  for (const auto& [event, region] : updates) {
    ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), region, event);
  }
}

}  // namespace delta
