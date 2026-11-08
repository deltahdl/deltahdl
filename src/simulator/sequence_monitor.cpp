#include "simulator/sequence_monitor.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/evaluation.h"
#include "simulator/instance_bindings.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sequence_flatten.h"
#include "simulator/sequence_local_flow.h"
#include "simulator/sequence_locals.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_name_tables.h"
#include "simulator/stmt_exec_assertion_internal.h"
#include "simulator/sva_engine_sampling.h"
#include "simulator/variable.h"

namespace delta {

namespace {

struct LinearAttempt {
  size_t pos;
  uint32_t waited;
  std::vector<Logic4Vec> locals;
  uint32_t count = 0;
  bool repeating = false;
  bool crossed_zero = false;
  uint32_t flow_pick = 0;
  LinearSequenceAttempt* sub = nullptr;
  bool sub_begins = false;
};

bool OperandClockTicked(const LinearSequence& body, size_t pos,
                        SimContext& ctx) {
  uint32_t ticked = ctx.AssertionSamples().ClockTicks();
  int clock = OperandClockIndex(body, pos);
  return clock >= 32 || ((ticked >> clock) & 1u) != 0;
}

bool EvalOperand(const LinearSequence& body, LinearAttempt& attempt,
                 SimContext& ctx, Arena& arena) {
  uint32_t pick = attempt.flow_pick;
  attempt.flow_pick = 0;
  AttemptLocalsScope scope(body.locals, attempt.locals, ctx);
  const std::vector<SeqMatchAssign>& items = body.match_items[attempt.pos];
  scope.AssignItems(items, true, arena);
  const bool kHeld =
      EvalExpr(body.operands[attempt.pos], ctx, arena).IsTruthy();
  ctx.AssertionSamples().NoteOperand(body.operands[attempt.pos], kHeld);
  if (!kHeld) return false;
  TakeFlowedLocals(body.operands[attempt.pos], pick, ctx, arena);
  scope.AssignItems(items, false, arena);
  return true;
}

bool WithinDelay(const SeqCycleDelay& delay, uint32_t waited) {
  return waited >= delay.min && waited <= delay.max;
}

void CarryAttempt(LinearAttempt attempt, const SeqCycleDelay& delay,
                  std::vector<LinearAttempt>& carry) {
  if (attempt.flow_pick != 0) return;
  if (attempt.waited >= delay.max) return;
  if (delay.max == SeqCycleDelay::kUnbounded && attempt.waited > delay.min) {
    attempt.waited = delay.min;
  }
  if (attempt.locals.empty()) {
    for (const auto& kept : carry) {
      if (kept.pos == attempt.pos && kept.waited == attempt.waited &&
          kept.count == attempt.count && kept.repeating == attempt.repeating &&
          kept.crossed_zero == attempt.crossed_zero) {
        return;
      }
    }
  }
  carry.push_back(std::move(attempt));
}

struct TickStep {
  const LinearSequence& body;
  std::vector<LinearAttempt>& pending;
  std::vector<LinearAttempt>& carry;
  SimContext& ctx;
  Arena& arena;
  bool matched = false;
  std::vector<std::vector<Logic4Vec>>* ended = nullptr;
};

void MatchAt(TickStep& step, const LinearAttempt& attempt) {
  step.matched = true;
  if (step.ended != nullptr) step.ended->push_back(attempt.locals);
}

void EndOperand(TickStep& step, LinearAttempt& advanced) {
  if (advanced.pos + 1 == step.body.operands.size()) {
    MatchAt(step, advanced);
    return;
  }
  LinearAttempt next{advanced.pos + 1, 0, advanced.locals};
  const SeqCycleDelay& delay = step.body.delays[next.pos];
  next.crossed_zero =
      delay.max == 0 && OperandClockIndex(step.body, next.pos) !=
                            OperandClockIndex(step.body, advanced.pos);
  step.pending.push_back(std::move(next));
}

void KeepRepeating(TickStep& step, LinearAttempt advanced) {
  advanced.waited = 0;
  advanced.repeating = true;
  step.carry.push_back(std::move(advanced));
}

void StepConsecutive(TickStep& step, const LinearAttempt& attempt,
                     const SeqRepetition& rep) {
  if (attempt.count >= rep.max) return;
  LinearAttempt advanced = attempt;
  if (!EvalOperand(step.body, advanced, step.ctx, step.arena)) return;
  advanced.count = attempt.count + 1;
  if (advanced.count >= rep.min) EndOperand(step, advanced);
  if (advanced.count < rep.max) KeepRepeating(step, std::move(advanced));
}

void StepNonconsecutive(TickStep& step, const LinearAttempt& attempt,
                        const SeqRepetition& rep) {
  LinearAttempt advanced = attempt;
  bool holds = EvalOperand(step.body, advanced, step.ctx, step.arena);
  bool extends = rep.kind == SeqRepetition::Kind::kNonconsecutive;
  if (holds) {
    advanced.count = attempt.count + 1;
    if (advanced.count > rep.max) return;
    if (advanced.count >= rep.min) EndOperand(step, advanced);
    if (advanced.count == rep.max && !extends) return;
  } else if (extends && attempt.count >= rep.min) {
    EndOperand(step, advanced);
  }
  KeepRepeating(step, std::move(advanced));
}

void EndNestedIteration(TickStep& step, const LinearAttempt& holder) {
  const SeqRepetition& rep = step.body.repetitions[holder.pos];
  LinearAttempt ended = holder;
  ended.sub = nullptr;
  {
    AttemptLocalsScope scope(step.body.locals, ended.locals, step.ctx);
    scope.AssignItems(step.body.match_items[holder.pos], false, step.arena);
  }
  if (rep.kind != SeqRepetition::Kind::kConsecutive) {
    EndOperand(step, ended);
    return;
  }
  ended.count = holder.count + 1;
  if (ended.count >= rep.min) EndOperand(step, ended);
  if (ended.count >= rep.max) return;
  ended.sub =
      NewSequenceAttempt(*NestedOperand(step.body, holder.pos), step.arena);
  ended.sub_begins = true;
  step.carry.push_back(std::move(ended));
}

void StepNested(TickStep& step, LinearAttempt holder, bool begin) {
  const LinearSequence& nested = *NestedOperand(step.body, holder.pos);
  SequenceStep result = SequenceStep::kFailed;
  {
    AttemptLocalsScope scope(step.body.locals, holder.locals, step.ctx);
    result =
        StepSequenceAttempt(nested, *holder.sub, begin, step.ctx, step.arena);
  }
  if (result == SequenceStep::kMatched ||
      result == SequenceStep::kMatchedLast) {
    EndNestedIteration(step, holder);
  }
  if (result == SequenceStep::kPending || result == SequenceStep::kMatched) {
    step.carry.push_back(std::move(holder));
  }
}

void BeginNested(TickStep& step, LinearAttempt attempt,
                 const LinearSequence& nested) {
  attempt.sub = NewSequenceAttempt(nested, step.arena);
  StepNested(step, std::move(attempt), true);
}

void ArriveAtOperand(TickStep& step, const LinearAttempt& attempt,
                     const SeqRepetition& rep) {
  const LinearSequence* nested = NestedOperand(step.body, attempt.pos);
  if (rep.kind == SeqRepetition::Kind::kNone) {
    LinearAttempt advanced = attempt;
    if (nested != nullptr) {
      BeginNested(step, std::move(advanced), *nested);
    } else if (EvalOperand(step.body, advanced, step.ctx, step.arena)) {
      EndOperand(step, advanced);
    }
    return;
  }
  if (rep.kind != SeqRepetition::Kind::kConsecutive) {
    StepNonconsecutive(step, attempt, rep);
    return;
  }
  if (rep.min == 0 && attempt.pos + 1 < step.body.operands.size()) {
    step.pending.push_back({attempt.pos + 1, 1, attempt.locals});
  }
  if (nested == nullptr) {
    StepConsecutive(step, attempt, rep);
  } else if (rep.max > 0) {
    BeginNested(step, attempt, *nested);
  }
}

bool EndsAsTrailingEmpty(const TickStep& step, const LinearAttempt& attempt) {
  const SeqRepetition& rep = step.body.repetitions[attempt.pos];
  if (attempt.repeating || rep.kind != SeqRepetition::Kind::kConsecutive) {
    return false;
  }
  if (rep.min != 0 || attempt.pos + 1 != step.body.operands.size()) {
    return false;
  }
  return WithinDelay(step.body.delays[attempt.pos], attempt.waited + 1);
}

bool InsideThroughout(const TickStep& step, const LinearAttempt& attempt,
                      const SeqThroughout& guard) {
  if (attempt.pos < guard.first || attempt.pos > guard.last) return false;
  if (attempt.pos > guard.first || attempt.repeating) return true;
  if (guard.begins_at_read) return false;
  return attempt.waited + guard.lead >= step.body.delays[guard.first].min;
}

bool ThroughoutsBeginningHereHold(TickStep& step, LinearAttempt& attempt) {
  for (const SeqThroughout& guard : step.body.throughouts) {
    if (!guard.begins_at_read || guard.first != attempt.pos) continue;
    AttemptLocalsScope scope(step.body.locals, attempt.locals, step.ctx);
    if (!EvalExpr(guard.cond, step.ctx, step.arena).IsTruthy()) return false;
  }
  return true;
}

bool ThroughoutHolds(TickStep& step, LinearAttempt& attempt) {
  for (const SeqThroughout& guard : step.body.throughouts) {
    if (!InsideThroughout(step, attempt, guard)) continue;
    AttemptLocalsScope scope(step.body.locals, attempt.locals, step.ctx);
    if (!EvalExpr(guard.cond, step.ctx, step.arena).IsTruthy()) return false;
  }
  return true;
}

void ForkPerFlowedMatch(TickStep& step, const LinearAttempt& attempt) {
  if (attempt.repeating || attempt.flow_pick != 0 ||
      !OperandClockTicked(step.body, attempt.pos, step.ctx) ||
      !WithinDelay(step.body.delays[attempt.pos], attempt.waited)) {
    return;
  }
  const std::vector<DeclaredNameTables::MatchLocals>* matches =
      FlowedMatches(step.body.operands[attempt.pos], step.ctx);
  if (matches == nullptr) return;
  for (uint32_t i = 1; i < matches->size(); ++i) {
    LinearAttempt copy = attempt;
    copy.flow_pick = i;
    step.pending.push_back(std::move(copy));
  }
}

void StepAttempt(TickStep& step, LinearAttempt attempt) {
  if (!OperandClockTicked(step.body, attempt.pos, step.ctx)) {
    step.carry.push_back(std::move(attempt));
    return;
  }
  const SeqCycleDelay& delay = step.body.delays[attempt.pos];
  const SeqRepetition& rep = step.body.repetitions[attempt.pos];
  if (!ThroughoutHolds(step, attempt)) return;
  if (attempt.sub != nullptr) {
    bool begins = std::exchange(attempt.sub_begins, false);
    StepNested(step, std::move(attempt), begins);
    return;
  }
  if (EndsAsTrailingEmpty(step, attempt)) MatchAt(step, attempt);
  if (attempt.repeating) {
    if (rep.kind == SeqRepetition::Kind::kConsecutive) {
      StepConsecutive(step, attempt, rep);
    } else {
      StepNonconsecutive(step, attempt, rep);
    }
    return;
  }
  if (WithinDelay(delay, attempt.waited) &&
      ThroughoutsBeginningHereHold(step, attempt)) {
    ArriveAtOperand(step, attempt, rep);
  }
  if (rep.kind == SeqRepetition::Kind::kGoto ||
      rep.kind == SeqRepetition::Kind::kNonconsecutive) {
    if (WithinDelay(delay, attempt.waited)) return;
  }
  CarryAttempt(std::move(attempt), delay, step.carry);
}

std::vector<LinearAttempt> TickPending(const LinearSequence& body,
                                       const std::vector<LinearAttempt>& active,
                                       SimContext& ctx, Arena& arena,
                                       bool begin_attempt) {
  std::vector<LinearAttempt> pending;
  pending.reserve(active.size() + 1);
  for (LinearAttempt attempt : active) {
    if (OperandClockTicked(body, attempt.pos, ctx)) {
      if (attempt.crossed_zero) {
        attempt.crossed_zero = false;
      } else {
        ++attempt.waited;
      }
    }
    pending.push_back(std::move(attempt));
  }
  if (begin_attempt) {
    pending.push_back({0, 0, InitialLocals(body.locals, ctx, arena)});
  }
  return pending;
}

void StepPending(TickStep& step) {
  while (!step.pending.empty()) {
    LinearAttempt attempt = std::move(step.pending.back());
    step.pending.pop_back();
    ForkPerFlowedMatch(step, attempt);
    StepAttempt(step, std::move(attempt));
  }
}

bool AdvanceLinearAttempts(const LinearSequence& body,
                           std::vector<LinearAttempt>& active, SimContext& ctx,
                           Arena& arena, bool begin_attempt) {
  std::vector<LinearAttempt> pending =
      TickPending(body, active, ctx, arena, begin_attempt);
  std::vector<LinearAttempt> carry;
  TickStep step{body, pending, carry, ctx, arena};
  StepPending(step);
  active = std::move(carry);
  return step.matched;
}

struct IntersectAttempt {
  std::vector<std::vector<LinearAttempt>> active;
};

const LinearSequence* IntersectOperandOf(const LinearSequence& chain,
                                         size_t i) {
  return i == 0 ? &chain : &chain.intersects[i - 1];
}

IntersectAttempt FreshIntersectAttempt(const LinearSequence& chain) {
  return IntersectAttempt{
      std::vector<std::vector<LinearAttempt>>(chain.intersects.size() + 1)};
}

bool AdvanceIntersectAttempt(const LinearSequence& chain,
                             IntersectAttempt& attempt, bool begin,
                             SimContext& ctx, Arena& arena) {
  bool all_matched_now = true;
  for (size_t i = 0; i < attempt.active.size(); ++i) {
    if (!AdvanceLinearAttempts(*IntersectOperandOf(chain, i), attempt.active[i],
                               ctx, arena, begin)) {
      all_matched_now = false;
    }
  }
  return all_matched_now;
}

bool IntersectAttemptIsSpent(const IntersectAttempt& attempt) {
  for (const auto& active : attempt.active) {
    if (active.empty()) return true;
  }
  return false;
}

struct AndAttempt {
  std::vector<IntersectAttempt> active;
  std::vector<bool> matched;
};

const LinearSequence* ChainOf(const LinearSequence& body, size_t i) {
  return i == 0 ? &body : &body.conjuncts[i - 1];
}

AndAttempt FreshAndAttempt(const LinearSequence& body) {
  size_t chains = body.conjuncts.size() + 1;
  AndAttempt fresh{std::vector<IntersectAttempt>(chains),
                   std::vector<bool>(chains, false)};
  for (size_t i = 0; i < chains; ++i) {
    fresh.active[i] = FreshIntersectAttempt(*ChainOf(body, i));
  }
  return fresh;
}

bool AdvanceAndAttempt(const LinearSequence& body, AndAttempt& attempt,
                       bool begin, SimContext& ctx, Arena& arena) {
  bool matched_now = false;
  bool all_matched = true;
  for (size_t i = 0; i < attempt.active.size(); ++i) {
    if (AdvanceIntersectAttempt(*ChainOf(body, i), attempt.active[i], begin,
                                ctx, arena)) {
      matched_now = true;
      attempt.matched[i] = true;
    }
    if (!attempt.matched[i]) all_matched = false;
  }
  return matched_now && all_matched;
}

bool AndAttemptIsSpent(const AndAttempt& attempt) {
  bool any_active = false;
  bool all_matched = true;
  for (size_t i = 0; i < attempt.active.size(); ++i) {
    if (!IntersectAttemptIsSpent(attempt.active[i])) any_active = true;
    if (!attempt.matched[i]) all_matched = false;
  }
  if (all_matched && !any_active) return true;
  for (size_t i = 0; i < attempt.active.size(); ++i) {
    if (!attempt.matched[i] && IntersectAttemptIsSpent(attempt.active[i])) {
      return true;
    }
  }
  return false;
}

bool AdvanceConjunction(const LinearSequence& body,
                        std::vector<AndAttempt>& attempts, SimContext& ctx,
                        Arena& arena) {
  bool matched = false;
  for (AndAttempt& attempt : attempts) {
    if (AdvanceAndAttempt(body, attempt, false, ctx, arena)) matched = true;
  }
  AndAttempt fresh = FreshAndAttempt(body);
  if (AdvanceAndAttempt(body, fresh, true, ctx, arena)) matched = true;
  attempts.push_back(std::move(fresh));
  std::vector<AndAttempt> kept;
  for (AndAttempt& attempt : attempts) {
    if (!AndAttemptIsSpent(attempt)) kept.push_back(std::move(attempt));
  }
  attempts = std::move(kept);
  return matched;
}

struct OperandAttempts {
  std::vector<LinearAttempt> linear;
  std::vector<AndAttempt> conjunctive;
};

bool AdvanceOperand(const LinearSequence& body, OperandAttempts& attempts,
                    SimContext& ctx, Arena& arena) {
  if (body.conjuncts.empty() && body.intersects.empty()) {
    return AdvanceLinearAttempts(body, attempts.linear, ctx, arena, true);
  }
  return AdvanceConjunction(body, attempts.conjunctive, ctx, arena);
}

struct FirstMatchAttempt {
  std::vector<AndAttempt> operands;
  const InstanceBindings* bindings = nullptr;
  uint64_t started = 0;
};

const LinearSequence* OrOperandOf(const LinearSequence& body, size_t i) {
  return i == 0 ? &body : &body.alternatives[i - 1];
}

FirstMatchAttempt FreshFirstMatchAttempt(const LinearSequence& body) {
  FirstMatchAttempt fresh;
  for (size_t i = 0; i <= body.alternatives.size(); ++i) {
    fresh.operands.push_back(FreshAndAttempt(*OrOperandOf(body, i)));
  }
  return fresh;
}

bool AdvanceFirstMatchAttempt(const LinearSequence& body,
                              FirstMatchAttempt& attempt, bool begin,
                              SimContext& ctx, Arena& arena) {
  bool matched = false;
  for (size_t i = 0; i < attempt.operands.size(); ++i) {
    if (AdvanceAndAttempt(*OrOperandOf(body, i), attempt.operands[i], begin,
                          ctx, arena)) {
      matched = true;
    }
  }
  return matched;
}

bool FirstMatchAttemptIsSpent(const FirstMatchAttempt& attempt) {
  for (const AndAttempt& operand : attempt.operands) {
    if (!AndAttemptIsSpent(operand)) return false;
  }
  return true;
}

bool AdvanceFirstMatch(const LinearSequence& body,
                       std::vector<FirstMatchAttempt>& attempts,
                       SimContext& ctx, Arena& arena) {
  attempts.push_back(FreshFirstMatchAttempt(body));
  bool matched = false;
  std::vector<FirstMatchAttempt> kept;
  for (size_t i = 0; i < attempts.size(); ++i) {
    bool begin = i + 1 == attempts.size();
    if (AdvanceFirstMatchAttempt(body, attempts[i], begin, ctx, arena)) {
      matched = true;
    } else if (!FirstMatchAttemptIsSpent(attempts[i])) {
      kept.push_back(std::move(attempts[i]));
    }
  }
  attempts = std::move(kept);
  return matched;
}

struct BodyAttempts {
  std::vector<FirstMatchAttempt> first_match;
  OperandAttempts body;
  std::vector<OperandAttempts> alternatives;
};

bool AdvanceBody(const LinearSequence& body, BodyAttempts& attempts,
                 SimContext& ctx, Arena& arena) {
  if (body.first_match) {
    return AdvanceFirstMatch(body, attempts.first_match, ctx, arena);
  }
  bool matched = AdvanceOperand(body, attempts.body, ctx, arena);
  for (size_t i = 0; i < body.alternatives.size(); ++i) {
    if (AdvanceOperand(body.alternatives[i], attempts.alternatives[i], ctx,
                       arena)) {
      matched = true;
    }
  }
  return matched;
}

void FireSequenceEndpoint(SimContext& ctx, const std::string& ep_name) {
  auto* var = ctx.FindVariable(ep_name);
  if (!var) return;
  ctx.SetEventTriggered(ep_name);
  auto pending = std::move(var->watchers);
  var->watchers.clear();
  auto& sched = ctx.GetScheduler();
  Region region = ctx.IsReactiveContext() ? Region::kReactive : Region::kActive;
  for (auto& cb : pending) {
    auto* event = sched.GetEventPool().Acquire();
    event->callback = [var, watcher = std::move(cb)]() mutable {
      if (!watcher()) var->AddWatcher(std::move(watcher));
    };
    sched.ScheduleEvent(ctx.CurrentTime(), region, event);
  }
}

bool KeepsMatchLocals(const LinearSequence& body) {
  return !body.locals.empty() && !body.first_match &&
         body.alternatives.empty() && body.conjuncts.empty() &&
         body.intersects.empty();
}

bool AdvanceKeepingLocals(const LinearSequence& body, BodyAttempts& active,
                          const std::string& ep_name, SimContext& ctx,
                          Arena& arena) {
  std::vector<LinearAttempt>& linear = active.body.linear;
  std::vector<LinearAttempt> pending =
      TickPending(body, linear, ctx, arena, true);
  std::vector<LinearAttempt> carry;
  std::vector<std::vector<Logic4Vec>> ended;
  TickStep step{body, pending, carry, ctx, arena};
  step.ended = &ended;
  StepPending(step);
  linear = std::move(carry);
  if (!step.matched) return false;
  ctx.RecordEndpointLocals(ep_name, ctx.CurrentTime().ticks,
                           NamedMatchLocals(body.locals, ended));
  return true;
}

}  // namespace

SimCoroutine MakeSequenceMonitorCoroutine(LinearSequence body,
                                          std::vector<EventExpr> clock,
                                          std::string ep_name, SimContext& ctx,
                                          Arena& arena) {
  BodyAttempts active;
  active.alternatives.resize(body.alternatives.size());
  std::vector<const Expr*> past_sites;
  CollectPastDirectedSites(body, past_sites);
  bool keeps_locals = KeepsMatchLocals(body);
  while (!ctx.StopRequested()) {
    co_await EventAwaiter{ctx, clock, arena};
    co_await RegionAwaiter{ctx, Region::kObserved};
    auto& samples = ctx.AssertionSamples();
    bool outer_evaluating_property = samples.EvaluatingProperty();
    samples.SetEvaluatingProperty(true);
    for (const Expr* site : past_sites) EvalExpr(site, ctx, arena);
    bool matched = keeps_locals
                       ? AdvanceKeepingLocals(body, active, ep_name, ctx, arena)
                       : AdvanceBody(body, active, ctx, arena);
    samples.SetEvaluatingProperty(outer_evaluating_property);
    if (matched) FireSequenceEndpoint(ctx, ep_name);
  }
}

struct LinearSequenceAttempt {
  FirstMatchAttempt attempt;
};

LinearSequenceAttempt* NewSequenceAttempt(const LinearSequence& body,
                                          Arena& arena) {
  auto* attempt = arena.Create<LinearSequenceAttempt>();
  attempt->attempt = FreshFirstMatchAttempt(body);
  return attempt;
}

SequenceStep StepSequenceAttempt(const LinearSequence& body,
                                 LinearSequenceAttempt& attempt, bool begin,
                                 SimContext& ctx, Arena& arena) {
  bool matched =
      AdvanceFirstMatchAttempt(body, attempt.attempt, begin, ctx, arena);
  bool spent = FirstMatchAttemptIsSpent(attempt.attempt);
  if (matched) {
    return spent ? SequenceStep::kMatchedLast : SequenceStep::kMatched;
  }
  return spent ? SequenceStep::kFailed : SequenceStep::kPending;
}

struct SequencePropertyState {
  LinearSequence body;
  std::vector<const Expr*> past_sites;
  std::vector<FirstMatchAttempt> attempts;
  SimTime advanced_at{UINT64_MAX};
};

SequencePropertyState* CreateSequencePropertyState(const ModuleItem* seq,
                                                   SimContext& ctx,
                                                   Arena& arena) {
  auto* state = arena.Create<SequencePropertyState>();
  if (!FlattenLinearSequence(seq, ctx, arena, state->body)) return nullptr;
  CollectPastDirectedSites(state->body, state->past_sites);
  return state;
}

namespace {

std::vector<SequenceOutcome> DisableSequenceAttempts(
    SequencePropertyState& state, const SequenceTick& tick, SimTime now) {
  std::vector<SequenceOutcome> outcomes;
  outcomes.reserve(state.attempts.size() + tick.instances.size());
  for (const FirstMatchAttempt& attempt : state.attempts) {
    outcomes.push_back(
        {SequenceVerdict::kDisabled, attempt.bindings, attempt.started});
  }
  for (const InstanceBindings* bindings : tick.instances) {
    outcomes.push_back({SequenceVerdict::kDisabled, bindings, now.ticks});
  }
  state.attempts.clear();
  return outcomes;
}

bool SettleSequenceAttempt(const FirstMatchAttempt& attempt, bool matched,
                           bool every_match,
                           std::vector<SequenceOutcome>& outcomes) {
  bool spent = FirstMatchAttemptIsSpent(attempt);
  if (matched || spent) {
    outcomes.push_back(
        {matched ? SequenceVerdict::kMatched : SequenceVerdict::kFailed,
         attempt.bindings, attempt.started});
  }
  return !spent && (!matched || every_match);
}

}  // namespace

std::vector<SequenceOutcome> AdvanceSequenceProperty(
    SequencePropertyState& state, const SequenceTick& tick, SimContext& ctx,
    Arena& arena) {
  std::vector<SequenceOutcome> outcomes;
  for (const Expr* site : state.past_sites) EvalExpr(site, ctx, arena);
  SimTime now = ctx.AssertionSamples().StepTime(ctx.CurrentTime());
  if (tick.disabled) return DisableSequenceAttempts(state, tick, now);
  size_t advanced = state.advanced_at == now ? state.attempts.size() : 0;
  state.advanced_at = now;
  for (const InstanceBindings* bindings : tick.instances) {
    state.attempts.push_back(FreshFirstMatchAttempt(state.body));
    state.attempts.back().bindings = bindings;
    state.attempts.back().started = now.ticks;
  }
  auto& samples = ctx.AssertionSamples();
  std::vector<FirstMatchAttempt> kept;
  for (size_t i = 0; i < state.attempts.size(); ++i) {
    if (i < advanced) {
      kept.push_back(std::move(state.attempts[i]));
      continue;
    }
    bool first = i + tick.instances.size() >= state.attempts.size();
    samples.SetInstanceBindings(state.attempts[i].bindings);
    samples.NoteAttemptStepped(state.attempts[i].started);
    bool matched = AdvanceFirstMatchAttempt(state.body, state.attempts[i],
                                            first, ctx, arena);
    samples.SetInstanceBindings(nullptr);
    if (SettleSequenceAttempt(state.attempts[i], matched, tick.every_match,
                              outcomes)) {
      kept.push_back(std::move(state.attempts[i]));
    }
  }
  state.attempts = std::move(kept);
  return outcomes;
}

std::vector<uint64_t> PendingSequenceStarts(
    const SequencePropertyState& state) {
  std::vector<uint64_t> starts;
  starts.reserve(state.attempts.size());
  for (const FirstMatchAttempt& attempt : state.attempts) {
    starts.push_back(attempt.started);
  }
  return starts;
}

std::size_t AbortSequencePropertyAttempts(SequencePropertyState& state) {
  return std::exchange(state.attempts, {}).size();
}

std::size_t AbortSequencePropertyAttemptAt(SequencePropertyState& state,
                                           uint64_t started) {
  return std::erase_if(state.attempts,
                       [started](const FirstMatchAttempt& attempt) {
                         return attempt.started == started;
                       });
}

}  // namespace delta
