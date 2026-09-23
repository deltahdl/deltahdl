#include "simulator/sequence_monitor.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/evaluation.h"
#include "simulator/expr_walk.h"
#include "simulator/instance_bindings.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sequence_flatten.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_exec.h"
#include "simulator/sva_engine_sampling.h"
#include "simulator/variable.h"

namespace delta {

uint32_t LocalWidth(TokenKind type_kw) {
  switch (type_kw) {
    case TokenKind::kKwByte:
      return 8;
    case TokenKind::kKwShortint:
      return 16;
    case TokenKind::kKwInt:
    case TokenKind::kKwInteger:
      return 32;
    case TokenKind::kKwLongint:
      return 64;
    default:
      return 1;
  }
}

namespace {

// One attempt of the sequence part way through: the operand it is to match
// next, the clock ticks that have passed since the operand before it matched,
// or since the attempt began for the first operand, and §16.10's local
// variables, of which each attempt holds its own copy, in the order of the
// flattened body's locals.
struct LinearAttempt {
  size_t pos;
  uint32_t waited;
  std::vector<Logic4Vec> locals;
  // §16.9.2: inside a repetition of the operand at pos, the iterations
  // matched so far; `repeating` once the attempt has arrived at a repeated
  // operand, after which it is kept from tick to tick by the repetition's
  // own rules rather than the operand's delay range.
  uint32_t count = 0;
  bool repeating = false;
  // §16.13.1: the attempt has just crossed to an operand on another clock
  // under `##0`, which is read at the nearest tick of that clock, the one
  // coincident with the crossing where there is one and the next one
  // otherwise, so the first tick of the new clock counts no wait.
  bool crossed_zero = false;
};

// §16.13.1: whether the clock the operand at `pos` is evaluated on ticked at
// this time step; every clock has where the property is on one clock.
bool OperandClockTicked(const LinearSequence& body, size_t pos,
                        SimContext& ctx) {
  uint32_t ticked = ctx.AssertionSamples().ClockTicks();
  int clock = OperandClockIndex(body, pos);
  return clock >= 32 || ((ticked >> clock) & 1u) != 0;
}

// §16.10 and §6.8: the state of a local declared with a data type keyword,
// and the value it holds before any assignment, x for a 4-state type and 0
// for a 2-state one.
bool LocalIs4State(TokenKind type_kw) {
  return type_kw == TokenKind::kKwLogic || type_kw == TokenKind::kKwReg ||
         type_kw == TokenKind::kKwInteger;
}

// §16.10: the initialization assignments are performed in the order the
// locals are declared, one's expression reading the locals declared before
// it as assigned, so each is stood up in a scope of its own as its value is
// found; a local without an initialization is unassigned, x for a 4-state
// type.
std::vector<Logic4Vec> InitialLocals(const std::vector<SeqLocalDecl>& decls,
                                     SimContext& ctx, Arena& arena) {
  std::vector<Logic4Vec> values;
  values.reserve(decls.size());
  ctx.PushScope();
  for (const SeqLocalDecl& decl : decls) {
    Logic4Vec value = MakeLogic4Vec(arena, LocalWidth(decl.type_kw));
    if (decl.init != nullptr) {
      value = ResizeToWidth(OwnRhsWords(EvalExpr(decl.init, ctx, arena), arena),
                            LocalWidth(decl.type_kw), arena);
    } else if (LocalIs4State(decl.type_kw)) {
      FillWithX(value);
    }
    Variable* var = ctx.CreateLocalVariable(decl.name, value.width);
    var->is_4state = LocalIs4State(decl.type_kw);
    var->value = value;
    values.push_back(value);
  }
  ctx.PopScope();
  return values;
}

// §16.11: a subroutine call attached to a sequence is executed at each end
// point, in the Reactive region like an action block, and does not hold the
// evaluation up; an argument passed by value reads the sampled value the
// match was evaluated with, so each argument is evaluated here, the attempt's
// locals in scope, and its value stands in for the expression while the call
// runs.
void ScheduleMatchCall(const Expr* call, SimContext& ctx, Arena& arena) {
  std::vector<std::pair<const Expr*, Logic4Vec>> snaps;
  for (const Expr* arg : call->args) {
    if (arg != nullptr) snaps.emplace_back(arg, EvalExpr(arg, ctx, arena));
  }
  auto* ev = ctx.GetScheduler().GetEventPool().Acquire();
  ev->callback = [call, snaps = std::move(snaps), &ctx, &arena]() {
    for (const auto& snap : snaps) {
      ctx.SetDeferredArgSnapshot(snap.first, snap.second);
    }
    if (!TryExecSystemCallTask(call, ctx, arena)) EvalExpr(call, ctx, arena);
    for (const auto& snap : snaps) ctx.ClearDeferredArgSnapshot(snap.first);
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kReactive, ev);
}

// §16.10: the attempt's locals stood up as variables of a scope of their own
// for the length of one operand's evaluation, read back into the attempt when
// the scope is popped, so an operand and its match items read and write the
// attempt's own copies.
class AttemptLocalsScope {
 public:
  AttemptLocalsScope(const std::vector<SeqLocalDecl>& decls,
                     LinearAttempt& attempt, SimContext& ctx)
      : attempt_(attempt), ctx_(ctx) {
    ctx_.PushScope();
    for (size_t i = 0; i < decls.size() && i < attempt.locals.size(); ++i) {
      Variable* var =
          ctx_.CreateLocalVariable(decls[i].name, attempt.locals[i].width);
      var->is_4state = LocalIs4State(decls[i].type_kw);
      var->value = attempt.locals[i];
      vars_.push_back(var);
    }
  }
  ~AttemptLocalsScope() {
    for (size_t i = 0; i < vars_.size(); ++i) {
      attempt_.locals[i] = vars_[i]->value;
    }
    ctx_.PopScope();
  }
  AttemptLocalsScope(const AttemptLocalsScope&) = delete;
  AttemptLocalsScope& operator=(const AttemptLocalsScope&) = delete;

  // §16.10: one match item, `lvar = rhs` or `lvar op= rhs`, assigning the
  // attempt's copy of the local; the assigned value takes words of its own.
  // §16.11: a subroutine call among the items is scheduled instead.
  void Assign(const SeqMatchAssign& item, Arena& arena) {
    if (item.call != nullptr) {
      ScheduleMatchCall(item.call, ctx_, arena);
      return;
    }
    if (item.local_copy != nullptr) {
      AssignLocalCopy(item, arena);
      return;
    }
    Variable* var = ctx_.FindLocalVariable(item.lvar);
    if (var == nullptr) return;
    Logic4Vec rhs = EvalExpr(item.rhs, ctx_, arena);
    if (item.op != TokenKind::kEq) {
      rhs = EvalBinaryOp(CompoundAssignBaseOp(item.op), var->value, rhs, arena);
    }
    var->value =
        ResizeToWidth(OwnRhsWords(rhs, arena), var->value.width, arena);
  }

 private:
  // §16.10 and §16.13.7: an item assigning a local of the named property the
  // sequence stands in, whose other expressions read the attempt's copy
  // through the same literal, so the literal is rewritten in place with the
  // value at the local's width, as the copy's initialization writes it.
  void AssignLocalCopy(const SeqMatchAssign& item, Arena& arena) {
    Logic4Vec held = EvalExpr(item.local_copy, ctx_, arena);
    Logic4Vec rhs = EvalExpr(item.rhs, ctx_, arena);
    if (item.op != TokenKind::kEq) {
      rhs = EvalBinaryOp(CompoundAssignBaseOp(item.op), held, rhs, arena);
    }
    *item.local_copy = *LiteralOfValue(
        ResizeToWidth(OwnRhsWords(rhs, arena), held.width, arena), arena);
  }

  LinearAttempt& attempt_;
  SimContext& ctx_;
  std::vector<Variable*> vars_;
};

// One operand of an attempt at this tick: the initialization items run before
// the Boolean is read, the Boolean is read over the attempt's locals, and the
// other match items run where it holds. Reports whether it held.
bool EvalOperand(const LinearSequence& body, LinearAttempt& attempt,
                 SimContext& ctx, Arena& arena) {
  AttemptLocalsScope scope(body.locals, attempt, ctx);
  const std::vector<SeqMatchAssign>& items = body.match_items[attempt.pos];
  for (const SeqMatchAssign& item : items) {
    if (item.init) scope.Assign(item, arena);
  }
  if (!EvalExpr(body.operands[attempt.pos], ctx, arena).IsTruthy()) {
    return false;
  }
  for (const SeqMatchAssign& item : items) {
    if (!item.init) scope.Assign(item, arena);
  }
  return true;
}

// §16.7: the delay before an operand is a range of clock ticks, and the
// operand is checked at every tick within it, so an attempt inside the range
// matches at each such tick the operand holds at and stays alive to the range's
// end. A delay with no upper bound keeps the attempt alive for the run, and
// once its wait has reached the lower bound every further tick reads the same,
// so its wait is held at that bound and the attempts that reach it coincide.
bool WithinDelay(const SeqCycleDelay& delay, uint32_t waited) {
  return waited >= delay.min && waited <= delay.max;
}

void CarryAttempt(LinearAttempt attempt, const SeqCycleDelay& delay,
                  std::vector<LinearAttempt>& carry) {
  if (attempt.waited >= delay.max) return;
  if (delay.max == SeqCycleDelay::kUnbounded && attempt.waited > delay.min) {
    attempt.waited = delay.min;
  }
  // Two attempts at one position and wait coincide only where they carry no
  // locals, an attempt's locals being its own.
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

// §16.14.5 always-semantics: one clock tick of every in-flight attempt, and of
// the fresh attempt this tick begins. An attempt whose operand's delay the
// tick falls within checks the operand: holding, it matches the sequence at
// its last operand or begins waiting for the next, a next operand with a `##0`
// before it checked at this same tick as §16.7 has the concatenation with a
// delay of 0 overlap; and whether or not it holds, the attempt stays for the
// later ticks of its range. Reports whether any attempt matched at this tick.
// What one tick of an attempt reads and writes: the sequence, the attempts
// to read again at this tick, at the operand after a match with a delay of 0
// to it, the ones kept for the next tick, whether the sequence matched at
// this tick, and the context the operands are evaluated in.
struct TickStep {
  const LinearSequence& body;
  std::vector<LinearAttempt>& pending;
  std::vector<LinearAttempt>& carry;
  SimContext& ctx;
  Arena& arena;
  bool matched = false;
};

// The attempt's operand has matched at this tick: the sequence ends here where
// it was the last, and otherwise an attempt at the next operand begins its
// wait here with the locals as written.
void EndOperand(TickStep& step, LinearAttempt& advanced) {
  if (advanced.pos + 1 == step.body.operands.size()) {
    step.matched = true;
    return;
  }
  LinearAttempt next{advanced.pos + 1, 0, advanced.locals};
  // §16.13.1: `##0` to an operand on another clock reads it at the nearest
  // tick of that clock, coincident or later.
  const SeqCycleDelay& delay = step.body.delays[next.pos];
  next.crossed_zero =
      delay.max == 0 && OperandClockIndex(step.body, next.pos) !=
                            OperandClockIndex(step.body, advanced.pos);
  step.pending.push_back(std::move(next));
}

// Keeps an attempt inside a repetition for the next tick.
void KeepRepeating(TickStep& step, LinearAttempt advanced) {
  advanced.waited = 0;
  advanced.repeating = true;
  step.carry.push_back(std::move(advanced));
}

// §16.9.2 consecutive repetition `b[*min:max]`: the operand matches at
// consecutive ticks, the repetition ending at the last; the whole may end
// after any number of matches from min to max, and a further match is read
// at the very next tick while fewer than max have been.
void StepConsecutive(TickStep& step, const LinearAttempt& attempt,
                     const SeqRepetition& rep) {
  // §16.9.2.1: `a[*0]` admits the empty match alone, so a match of a is not
  // an iteration of it.
  if (attempt.count >= rep.max) return;
  LinearAttempt advanced = attempt;
  if (!EvalOperand(step.body, advanced, step.ctx, step.arena)) return;
  advanced.count = attempt.count + 1;
  if (advanced.count >= rep.min) EndOperand(step, advanced);
  if (advanced.count < rep.max) KeepRepeating(step, std::move(advanced));
}

// §16.9.2 goto `b[->min:max]` and nonconsecutive `b[=min:max]` repetition:
// the operand matches at ticks that need not be consecutive, the whole ending
// at the last match after min to max of them, or, for the nonconsecutive
// form, at any later tick the operand does not hold at, before any further
// match.
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

// An attempt arriving at its operand within the delay range reads it: a
// plain operand ends where it holds, a repeated one begins its repetition,
// and an empty consecutive repetition also lets the attempt pass on, as
// §16.9.2.1 has `empty ##n seq` be `##(n-1) seq`.
void ArriveAtOperand(TickStep& step, const LinearAttempt& attempt,
                     const SeqRepetition& rep) {
  if (rep.kind == SeqRepetition::Kind::kNone) {
    LinearAttempt advanced = attempt;
    if (EvalOperand(step.body, advanced, step.ctx, step.arena)) {
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
  StepConsecutive(step, attempt, rep);
}

// One attempt at this tick: inside a repetition it steps by the repetition's
// rules; otherwise it reads its operand where the tick is within the delay
// range, and stays for the next tick while the range runs.
// §16.9.2.1: `seq ##n empty` is `seq ##(n-1) `true`, so an attempt owed a
// last operand that admits the empty match ends a tick before the delay to
// that operand would be up, and `seq ##0 empty` ends nowhere.
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

// §16.9.9: whether the attempt is inside the interval of a throughout at
// this tick: past its first operand and not past its last, or at the first
// operand, in its repetition or with the delay before the throughout up, the
// interval beginning where the guarded sequence begins, `lead` ticks before
// its first operand is read.
bool InsideThroughout(const TickStep& step, const LinearAttempt& attempt,
                      const SeqThroughout& guard) {
  if (attempt.pos < guard.first || attempt.pos > guard.last) return false;
  if (attempt.pos > guard.first || attempt.repeating) return true;
  return attempt.waited + guard.lead >= step.body.delays[guard.first].min;
}

// §16.9.9: an attempt inside the interval of a throughout whose condition
// does not hold at this tick is dropped, `(exp)[*0:$] intersect seq` having
// no match over an interval exp is false at a tick of.
bool ThroughoutHolds(TickStep& step, LinearAttempt& attempt) {
  for (const SeqThroughout& guard : step.body.throughouts) {
    if (!InsideThroughout(step, attempt, guard)) continue;
    AttemptLocalsScope scope(step.body.locals, attempt, step.ctx);
    if (!EvalExpr(guard.cond, step.ctx, step.arena).IsTruthy()) return false;
  }
  return true;
}

void StepAttempt(TickStep& step, LinearAttempt attempt) {
  // §16.13.1: an attempt at an operand on a clock that did not tick at this
  // time step waits as it is for a tick of that clock.
  if (!OperandClockTicked(step.body, attempt.pos, step.ctx)) {
    step.carry.push_back(std::move(attempt));
    return;
  }
  const SeqCycleDelay& delay = step.body.delays[attempt.pos];
  const SeqRepetition& rep = step.body.repetitions[attempt.pos];
  if (!ThroughoutHolds(step, attempt)) return;
  if (EndsAsTrailingEmpty(step, attempt)) step.matched = true;
  if (attempt.repeating) {
    if (rep.kind == SeqRepetition::Kind::kConsecutive) {
      StepConsecutive(step, attempt, rep);
    } else {
      StepNonconsecutive(step, attempt, rep);
    }
    return;
  }
  if (WithinDelay(delay, attempt.waited)) ArriveAtOperand(step, attempt, rep);
  // A goto or nonconsecutive repetition, once begun, waits by its own rules
  // rather than by the delay range before it.
  if (rep.kind == SeqRepetition::Kind::kGoto ||
      rep.kind == SeqRepetition::Kind::kNonconsecutive) {
    if (WithinDelay(delay, attempt.waited)) return;
  }
  CarryAttempt(std::move(attempt), delay, step.carry);
}

bool AdvanceLinearAttempts(const LinearSequence& body,
                           std::vector<LinearAttempt>& active, SimContext& ctx,
                           Arena& arena, bool begin_attempt) {
  std::vector<LinearAttempt> pending;
  pending.reserve(active.size() + 1);
  for (LinearAttempt attempt : active) {
    // §16.13.1: a tick of the clock the attempt's operand is evaluated on
    // is a tick of its wait, the first after crossing to it under `##0`
    // counting none; a step at which that clock did not tick is none.
    if (OperandClockTicked(body, attempt.pos, ctx)) {
      if (attempt.crossed_zero) {
        attempt.crossed_zero = false;
      } else {
        ++attempt.waited;
      }
    }
    pending.push_back(std::move(attempt));
  }
  // §16.10: a new attempt begins with a new copy of every local variable.
  if (begin_attempt) {
    pending.push_back({0, 0, InitialLocals(body.locals, ctx, arena)});
  }
  std::vector<LinearAttempt> carry;
  TickStep step{body, pending, carry, ctx, arena};
  while (!pending.empty()) {
    LinearAttempt attempt = std::move(pending.back());
    pending.pop_back();
    StepAttempt(step, std::move(attempt));
  }
  active = std::move(carry);
  return step.matched;
}

// §16.9.6: one attempt of `s1 intersect s2 ...`, begun at one tick: the
// attempts of the chain and of each of its intersects that tick began. The
// whole matches at a tick where every operand matches at it, the matches
// paired by their shared length; it is spent once any operand has no attempt
// in flight, no further pair being possible.
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

// Advances one intersect-attempt over every operand at this tick, the
// operands' own attempts begun where `begin` says this is the tick the
// intersect-attempt begins at. Reports whether the whole matched at this
// tick.
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

// §16.9.5: one attempt of `s1 and s2 ...`, begun at one tick: the attempts
// of each operand chain, an intersection of its own, that tick began, and
// whether each chain has matched since. The whole matches at a tick where
// every chain has matched by then and one matches at that tick, which is the
// later of the end points; it is dropped once no chain can go on, or every
// chain has matched and none has an attempt in flight.
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

// Advances one and-attempt over every chain at this tick, the chains' own
// attempts begun where `begin` says this is the tick the and-attempt begins
// at. Reports whether the whole matched at this tick.
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

// One tick of a conjunction: the and-attempts in flight advance, a new one
// begins, and the spent ones are dropped. Reports whether any matched.
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

// One tick of an `or` operand: a plain chain advances its own attempts, and a
// chain with intersects or conjuncts its and-attempts, whose attempts are
// kept apart by the tick they began at as the pairing of matches needs.
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

// §16.9.8: one attempt of `first_match(s)`, begun at one tick: an
// and-attempt for each `or` operand of s, all begun at that tick, so that the
// attempt's matches over every operand are kept together. The whole matches
// at the first tick any operand matches at, every match ending there being a
// match of the first_match, and is dropped then, the matches that would end
// later discarded; it is dropped as well once no operand can go on.
struct FirstMatchAttempt {
  std::vector<AndAttempt> operands;
  // §16.14.6.1: the values the instance this attempt is saved when it was
  // queued, bound around every step of the attempt; nullptr for a static
  // assertion's attempt.
  const InstanceBindings* bindings = nullptr;
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

// One tick of a first_match body: the attempts in flight advance, a new one
// begins, and those that matched or are spent are dropped. Reports whether
// any matched.
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

// The attempts of a whole body: those of a first_match body, kept apart by
// the tick they began at, or each `or` operand's own.
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
  // §16.9.7: the body's `or` operands are matched side by side, each with
  // attempts of its own, and the sequence reaches an end point at a tick any
  // of them ends at.
  bool matched = AdvanceOperand(body, attempts.body, ctx, arena);
  for (size_t i = 0; i < body.alternatives.size(); ++i) {
    if (AdvanceOperand(body.alternatives[i], attempts.alternatives[i], ctx,
                       arena)) {
      matched = true;
    }
  }
  return matched;
}

// §16.9.3: a sampled value function in a sequence is clocked by the
// sequence's clock, and the history it looks back through is sampled at
// every tick of that clock whether or not an attempt reads the operand at
// the tick -- `$rose(ready)` standing after `inst` in a chain still answers
// the tick before. The calls are collected once, over every chain of the
// body, and each is evaluated as the monitor resumes so that its sample for
// the tick is recorded; an attempt reading it records the same value over
// it.
bool IsPastDirectedCall(const Expr* e) {
  if (e->kind != ExprKind::kSystemCall) return false;
  return e->callee == "$past" || e->callee == "$rose" || e->callee == "$fell" ||
         e->callee == "$stable" || e->callee == "$changed";
}

void CollectPastDirectedSites(const LinearSequence& body,
                              std::vector<const Expr*>& sites) {
  ForEachLinearSequenceExpr(body, [&sites](const Expr* e) {
    ForEachSubExpr(e, [&sites](const Expr* sub) {
      if (IsPastDirectedCall(sub)) sites.push_back(sub);
    });
  });
}

// §16.13.6: mark the sequence endpoint event triggered and wake its waiters,
// mirroring the named-event `-> ev` trigger path (stmt_exec.cpp).
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
    event->callback = std::move(cb);
    sched.ScheduleEvent(ctx.CurrentTime(), region, event);
  }
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
  while (!ctx.StopRequested()) {
    co_await EventAwaiter{ctx, clock, arena};
    for (const Expr* site : past_sites) EvalExpr(site, ctx, arena);
    // §16.14.5: a new evaluation attempt begins at every clock tick, which
    // each advance adds beside the ones in flight.
    if (AdvanceBody(body, active, ctx, arena)) {
      FireSequenceEndpoint(ctx, ep_name);
    }
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

// §16.12.2: one evaluation attempt of a sequential property is one attempt
// of its sequence, begun at the tick the property's attempt begins at and
// kept apart from the others as first_match keeps them; it holds where the
// sequence matches and fails where no attempt of the sequence can go on, a
// prefix witnessing that the sequence cannot match.
struct SequencePropertyState {
  LinearSequence body;
  std::vector<const Expr*> past_sites;
  std::vector<FirstMatchAttempt> attempts;
  // The time step the attempts last advanced at, §16.14.6.3's second pass
  // of one step beginning attempts without advancing those again.
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

std::vector<SequenceOutcome> AdvanceSequenceProperty(
    SequencePropertyState& state, const SequenceTick& tick, SimContext& ctx,
    Arena& arena) {
  std::vector<SequenceOutcome> outcomes;
  for (const Expr* site : state.past_sites) EvalExpr(site, ctx, arena);
  // §16.12: a disable condition true at any tick of an attempt disables it,
  // and the attempts beginning at this tick with it.
  if (tick.disabled) {
    state.attempts.clear();
    return outcomes;
  }
  // §16.14.6.3: at a second pass of one time step the attempts already
  // advanced at it advance no more; the new ones begin.
  SimTime now = ctx.CurrentTime();
  size_t advanced = state.advanced_at == now ? state.attempts.size() : 0;
  state.advanced_at = now;
  for (const InstanceBindings* bindings : tick.instances) {
    state.attempts.push_back(FreshFirstMatchAttempt(state.body));
    state.attempts.back().bindings = bindings;
  }
  auto& samples = ctx.AssertionSamples();
  std::vector<FirstMatchAttempt> kept;
  for (size_t i = 0; i < state.attempts.size(); ++i) {
    if (i < advanced) {
      kept.push_back(std::move(state.attempts[i]));
      continue;
    }
    bool first = i + tick.instances.size() >= state.attempts.size();
    // §16.14.6.1: the attempt reads the values its instance saved.
    samples.SetInstanceBindings(state.attempts[i].bindings);
    bool matched = AdvanceFirstMatchAttempt(state.body, state.attempts[i],
                                            first, ctx, arena);
    samples.SetInstanceBindings(nullptr);
    bool spent = FirstMatchAttemptIsSpent(state.attempts[i]);
    if (matched) {
      outcomes.push_back(
          {SequenceVerdict::kMatched, state.attempts[i].bindings});
    } else if (spent) {
      outcomes.push_back(
          {SequenceVerdict::kFailed, state.attempts[i].bindings});
    }
    if (!spent && (!matched || tick.every_match)) {
      kept.push_back(std::move(state.attempts[i]));
    }
  }
  state.attempts = std::move(kept);
  return outcomes;
}

size_t PendingSequenceAttempts(const SequencePropertyState& state) {
  return state.attempts.size();
}

}  // namespace delta
