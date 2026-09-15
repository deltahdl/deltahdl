#include "simulator/sequence_monitor.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {
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
};

// §16.10 and §6.8: the width and state of a local declared with a data type
// keyword, and the value it holds before any assignment, x for a 4-state
// type and 0 for a 2-state one.
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

bool LocalIs4State(TokenKind type_kw) {
  return type_kw == TokenKind::kKwLogic || type_kw == TokenKind::kKwReg ||
         type_kw == TokenKind::kKwInteger;
}

std::vector<Logic4Vec> InitialLocals(const std::vector<SeqLocalDecl>& decls,
                                     SimContext& ctx, Arena& arena) {
  std::vector<Logic4Vec> values;
  values.reserve(decls.size());
  for (const SeqLocalDecl& decl : decls) {
    Logic4Vec value = MakeLogic4Vec(arena, LocalWidth(decl.type_kw));
    if (decl.init != nullptr) {
      value = ResizeToWidth(OwnRhsWords(EvalExpr(decl.init, ctx, arena), arena),
                            LocalWidth(decl.type_kw), arena);
    } else if (LocalIs4State(decl.type_kw)) {
      FillWithX(value);
    }
    values.push_back(value);
  }
  return values;
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
  void Assign(const SeqMatchAssign& item, Arena& arena) {
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
      if (kept.pos == attempt.pos && kept.waited == attempt.waited) return;
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
bool AdvanceLinearAttempts(const LinearSequence& body,
                           std::vector<LinearAttempt>& active, SimContext& ctx,
                           Arena& arena, bool begin_attempt) {
  std::vector<LinearAttempt> pending;
  pending.reserve(active.size() + 1);
  for (LinearAttempt attempt : active) {
    ++attempt.waited;
    pending.push_back(std::move(attempt));
  }
  // §16.10: a new attempt begins with a new copy of every local variable.
  if (begin_attempt) {
    pending.push_back({0, 0, InitialLocals(body.locals, ctx, arena)});
  }
  std::vector<LinearAttempt> carry;
  bool matched = false;
  while (!pending.empty()) {
    LinearAttempt attempt = std::move(pending.back());
    pending.pop_back();
    const SeqCycleDelay& delay = body.delays[attempt.pos];
    // The operand reads and writes the attempt's locals, so an attempt that
    // goes on to the next operand carries the values as written, and the one
    // kept for the later ticks of the range carries the values as they stood.
    LinearAttempt advanced = attempt;
    if (WithinDelay(delay, attempt.waited) &&
        EvalOperand(body, advanced, ctx, arena)) {
      if (advanced.pos + 1 == body.operands.size()) {
        matched = true;
      } else {
        pending.push_back({advanced.pos + 1, 0, std::move(advanced.locals)});
      }
    }
    CarryAttempt(std::move(attempt), delay, carry);
  }
  active = std::move(carry);
  return matched;
}

// §16.9.5: one attempt of `s1 and s2 ...`, begun at one tick: the attempts
// of each operand chain that tick began, and whether each chain has matched
// since. The whole matches at a tick where every chain has matched by then
// and one matches at that tick, which is the later of the end points; it is
// dropped once no chain can go on, or every chain has matched and none has an
// attempt in flight.
struct AndAttempt {
  std::vector<std::vector<LinearAttempt>> active;
  std::vector<bool> matched;
};

const LinearSequence& ChainOf(const LinearSequence& body, size_t i) {
  return i == 0 ? body : body.conjuncts[i - 1];
}

// Advances one and-attempt over every chain at this tick, the chains' own
// attempts begun where `begin` says this is the tick the and-attempt begins
// at. Reports whether the whole matched at this tick.
bool AdvanceAndAttempt(const LinearSequence& body, AndAttempt& attempt,
                       bool begin, SimContext& ctx, Arena& arena) {
  bool matched_now = false;
  bool all_matched = true;
  for (size_t i = 0; i < attempt.active.size(); ++i) {
    if (AdvanceLinearAttempts(ChainOf(body, i), attempt.active[i], ctx, arena,
                              begin)) {
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
    if (!attempt.active[i].empty()) any_active = true;
    if (!attempt.matched[i]) all_matched = false;
  }
  if (all_matched && !any_active) return true;
  for (size_t i = 0; i < attempt.active.size(); ++i) {
    if (!attempt.matched[i] && attempt.active[i].empty()) return true;
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
  size_t chains = body.conjuncts.size() + 1;
  AndAttempt fresh{std::vector<std::vector<LinearAttempt>>(chains),
                   std::vector<bool>(chains, false)};
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
// chain with conjuncts its and-attempts.
struct OperandAttempts {
  std::vector<LinearAttempt> linear;
  std::vector<AndAttempt> conjunctive;
};

bool AdvanceOperand(const LinearSequence& body, OperandAttempts& attempts,
                    SimContext& ctx, Arena& arena) {
  if (body.conjuncts.empty()) {
    return AdvanceLinearAttempts(body, attempts.linear, ctx, arena, true);
  }
  return AdvanceConjunction(body, attempts.conjunctive, ctx, arena);
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
  // §16.9.7: the body's `or` operands are matched side by side, each with
  // attempts of its own, and the sequence reaches an end point at a tick any
  // of them ends at.
  OperandAttempts active;
  std::vector<OperandAttempts> alt_active(body.alternatives.size());
  while (!ctx.StopRequested()) {
    co_await EventAwaiter{ctx, clock, arena};
    // §16.14.5: a new evaluation attempt begins at every clock tick, which
    // each advance adds beside the ones in flight.
    bool matched = AdvanceOperand(body, active, ctx, arena);
    for (size_t i = 0; i < body.alternatives.size(); ++i) {
      if (AdvanceOperand(body.alternatives[i], alt_active[i], ctx, arena)) {
        matched = true;
      }
    }
    if (matched) FireSequenceEndpoint(ctx, ep_name);
  }
}

}  // namespace delta
