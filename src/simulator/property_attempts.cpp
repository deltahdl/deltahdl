#include "simulator/property_attempts.h"

#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/evaluation.h"
#include "simulator/expr_walk.h"
#include "simulator/sequence_flatten.h"
#include "simulator/sequence_monitor.h"
#include "simulator/sim_context.h"

namespace delta {
namespace {

// The verdict of one operand or of the tree over it: decided true or false,
// or not yet.
enum class Tri : uint8_t { kPending, kTrue, kFalse };

// The flattened sequence of each sequence node of the tree, an antecedent's
// among them, keyed by the node; flattened once for every attempt.
struct FlatSequence {
  const PropertyExprNode* node;
  LinearSequence body;
};

// The state of one node of the tree within one attempt: a leaf's verdict
// once decided and a sequence's attempt while it is in flight; an
// operator's operands' states; and, for an implication, the antecedent's
// attempt with the consequent's states begun at its matches, one to begin
// at the next tick where the implication is nonoverlapped, and whether the
// antecedent can match no more.
struct NodeState {
  Tri verdict = Tri::kPending;
  LinearSequenceAttempt* attempt = nullptr;
  std::vector<NodeState*> operands;
  std::vector<NodeState*> consequents;
  bool spawn_next = false;
  bool antecedent_done = false;
  // §16.12.6: the condition as read at the attempt's tick.
  bool condition = false;
  // §16.12.10: the ticks a nexttime has still to wait before its operand
  // begins, and whether the operand has begun; §16.12.11: the ticks an
  // always has still to wait before its range, and the ticks of the range
  // at which an operand attempt has still to begin, UINT64_MAX where the
  // range is unbounded.
  uint64_t wait = 0;
  bool begun = false;
  uint64_t remaining = 0;
  // §16.12.12: an until's attempts of its second operand, one begun at each
  // tick beside the first operand's in `consequents`, and the index of the
  // first tick not yet decided in `wait`.
  std::vector<NodeState*> seconds;
};

}  // namespace

struct PropertyTreeState {
  const PropertyExprNode* root = nullptr;
  std::vector<FlatSequence> sequences;
  std::vector<const Expr*> past_sites;
  std::vector<NodeState*> attempts;
};

namespace {

// §16.9.3: the sampled value functions the tree's booleans and sequences
// hold, sampled at every tick as a procedure's are.
bool IsPastDirectedCall(const Expr* e) {
  if (e->kind != ExprKind::kSystemCall) return false;
  return e->callee == "$past" || e->callee == "$rose" || e->callee == "$fell" ||
         e->callee == "$stable" || e->callee == "$changed";
}

void CollectPastDirectedSites(const Expr* e, std::vector<const Expr*>& sites) {
  ForEachSubExpr(e, [&sites](const Expr* sub) {
    if (IsPastDirectedCall(sub)) sites.push_back(sub);
  });
}

// The sequences of the tree flattened, each node's once; answers false where
// a sequence is not readable.
bool CollectSequences(const PropertyExprNode* node, PropertyTreeState& state,
                      SimContext& ctx, Arena& arena) {
  if (node->boolean != nullptr) {
    CollectPastDirectedSites(node->boolean, state.past_sites);
  }
  if (node->sequence != nullptr) {
    FlatSequence flat{node, LinearSequence{}};
    if (!FlattenLinearSequence(node->sequence, ctx, arena, flat.body)) {
      return false;
    }
    ForEachLinearSequenceExpr(flat.body, [&state](const Expr* e) {
      CollectPastDirectedSites(e, state.past_sites);
    });
    state.sequences.push_back(std::move(flat));
  }
  for (const PropertyExprNode* operand : node->operands) {
    if (!CollectSequences(operand, state, ctx, arena)) return false;
  }
  return true;
}

const LinearSequence& BodyOf(const PropertyTreeState& state,
                             const PropertyExprNode* node) {
  for (const FlatSequence& flat : state.sequences) {
    if (flat.node == node) return flat.body;
  }
  return state.sequences.front().body;
}

Tri Not(Tri t) {
  if (t == Tri::kPending) return t;
  return t == Tri::kTrue ? Tri::kFalse : Tri::kTrue;
}

bool Matched(SequenceStep step) {
  return step == SequenceStep::kMatched || step == SequenceStep::kMatchedLast;
}

Tri FromStep(SequenceStep step) {
  if (Matched(step)) return Tri::kTrue;
  if (step == SequenceStep::kFailed) return Tri::kFalse;
  return Tri::kPending;
}

Tri FromBool(bool b) { return b ? Tri::kTrue : Tri::kFalse; }

// §16.12.4 and §16.12.5 over the operands' verdicts: or is true where any
// operand is and false where every one is; and is false where any operand
// is and true where every one is; else the junction is not yet decided.
Tri Junction(bool is_or, const std::vector<Tri>& verdicts) {
  Tri decisive = is_or ? Tri::kTrue : Tri::kFalse;
  Tri result = is_or ? Tri::kFalse : Tri::kTrue;
  for (Tri t : verdicts) {
    if (t == decisive) result = decisive;
    if (t == Tri::kPending && result != decisive) result = Tri::kPending;
  }
  return result;
}

// §16.12.8 over two operands' verdicts: implies is true where the first is
// false or the second true, false where the first is true and the second
// false; iff is true where both are decided alike and false where decided
// apart; else not yet decided.
Tri Implies(Tri first, Tri second) {
  if (first == Tri::kFalse || second == Tri::kTrue) return Tri::kTrue;
  if (first == Tri::kTrue && second == Tri::kFalse) return Tri::kFalse;
  return Tri::kPending;
}

Tri Iff(Tri first, Tri second) {
  if (first == Tri::kPending || second == Tri::kPending) return Tri::kPending;
  return first == second ? Tri::kTrue : Tri::kFalse;
}

// The state of one attempt of the tree under `node`, its operators' operands
// stood up with it and its sequences' attempts to be begun at the first
// tick.
NodeState* NewNodeState(const PropertyExprNode* node, Arena& arena) {
  auto* state = arena.Create<NodeState>();
  for (const PropertyExprNode* operand : node->operands) {
    state->operands.push_back(NewNodeState(operand, arena));
  }
  return state;
}

// What one tick's steps read: the tree with its flattened sequences, the
// context and the arena.
struct StepContext {
  PropertyTreeState& tree;
  SimContext& ctx;
  Arena& arena;
};

// One tick of one attempt's node, `begin` where the tick is the one the
// attempt begins at, answering the node's verdict so far.
Tri Step(const PropertyExprNode* node, NodeState& state, StepContext& sc,
         bool begin);

Tri StepSequence(const PropertyExprNode* node, NodeState& state,
                 StepContext& sc, bool begin) {
  const LinearSequence& body = BodyOf(sc.tree, node);
  if (begin) state.attempt = NewSequenceAttempt(body, sc.arena);
  return FromStep(
      StepSequenceAttempt(body, *state.attempt, begin, sc.ctx, sc.arena));
}

Tri StepJunction(const PropertyExprNode* node, NodeState& state,
                 StepContext& sc, bool begin) {
  std::vector<Tri> verdicts;
  verdicts.reserve(node->operands.size());
  for (size_t i = 0; i < node->operands.size(); ++i) {
    verdicts.push_back(Step(node->operands[i], *state.operands[i], sc, begin));
  }
  return Junction(node->kind == PropertyExprNode::Kind::kOr, verdicts);
}

// §16.12.6: the condition is read at the attempt's tick, and the branch it
// selects is the property; the else absent is true.
Tri StepIfElse(const PropertyExprNode* node, NodeState& state, StepContext& sc,
               bool begin) {
  if (begin) {
    state.condition = EvalExpr(node->boolean, sc.ctx, sc.arena).IsTruthy();
  }
  Tri then_branch = Step(node->operands[0], *state.operands[0], sc, begin);
  Tri else_branch = node->operands.size() > 1
                        ? Step(node->operands[1], *state.operands[1], sc, begin)
                        : Tri::kTrue;
  return state.condition ? then_branch : else_branch;
}

// §16.12.7: one tick of the antecedent's attempt while it can still match,
// answering whether a consequent is to begin at this tick; a match of the
// nonoverlapped form begins one at the next tick instead.
bool StepAntecedent(const PropertyExprNode* node, NodeState& state,
                    StepContext& sc, bool begin) {
  if (state.antecedent_done) return false;
  const LinearSequence& body = BodyOf(sc.tree, node);
  if (begin) state.attempt = NewSequenceAttempt(body, sc.arena);
  SequenceStep step =
      StepSequenceAttempt(body, *state.attempt, begin, sc.ctx, sc.arena);
  if (step == SequenceStep::kFailed || step == SequenceStep::kMatchedLast) {
    state.antecedent_done = true;
  }
  if (!Matched(step)) return false;
  if (!node->strong) return true;
  state.spawn_next = true;
  return false;
}

// §16.12.7: the antecedent's attempt is stepped until it can match no more,
// and at each tick it matches at a consequent attempt begins, at that tick
// for `|->` and at the next for `|=>`; the implication is false as soon as
// a consequent is, and true once the antecedent can match no more and every
// consequent begun is true, no match of the antecedent making it true.
Tri StepImplication(const PropertyExprNode* node, NodeState& state,
                    StepContext& sc, bool begin) {
  const PropertyExprNode* consequent = node->operands[0];
  std::vector<Tri> verdicts;
  verdicts.reserve(state.consequents.size() + 1);
  for (NodeState* c : state.consequents) {
    verdicts.push_back(Step(consequent, *c, sc, false));
  }
  bool spawn_now = state.spawn_next;
  state.spawn_next = false;
  if (StepAntecedent(node, state, sc, begin)) spawn_now = true;
  if (spawn_now) {
    NodeState* c = NewNodeState(consequent, sc.arena);
    state.consequents.push_back(c);
    verdicts.push_back(Step(consequent, *c, sc, true));
  }
  Tri all = Junction(false, verdicts);
  if (all == Tri::kFalse) return Tri::kFalse;
  if (state.antecedent_done && !state.spawn_next && all == Tri::kTrue) {
    return Tri::kTrue;
  }
  return Tri::kPending;
}

// §16.12.10: the operand begins at the tick the count of ticks after the
// attempt's has passed, one where none was written, `nexttime [0]` at the
// attempt's own tick; until then the property is not decided.
Tri StepNexttime(const PropertyExprNode* node, NodeState& state,
                 StepContext& sc, bool begin) {
  if (begin) {
    state.wait = node->boolean != nullptr
                     ? EvalExpr(node->boolean, sc.ctx, sc.arena).ToUint64()
                     : 1;
  } else if (!state.begun) {
    --state.wait;
  }
  if (!state.begun && state.wait > 0) return Tri::kPending;
  bool first = !state.begun;
  state.begun = true;
  return Step(node->operands[0], *state.operands[0], sc, first);
}

uint64_t EvalCount(const Expr* e, StepContext& sc, uint64_t absent) {
  if (e == nullptr) return absent;
  return EvalExpr(e, sc.ctx, sc.arena).ToUint64();
}

// §16.12.11: an operand attempt begins at each tick of the range, and the
// always is false as soon as one is false and true once every tick of a
// bounded range has begun one and all are true.
Tri StepAlways(const PropertyExprNode* node, NodeState& state, StepContext& sc,
               bool begin) {
  const PropertyExprNode* operand = node->operands[0];
  if (begin) {
    state.wait = EvalCount(node->range_min, sc, 0);
    state.remaining = node->range_unbounded
                          ? UINT64_MAX
                          : EvalCount(node->range_max, sc, 0) - state.wait + 1;
  } else if (state.wait > 0) {
    --state.wait;
  }
  std::vector<Tri> verdicts;
  verdicts.reserve(state.consequents.size() + 1);
  for (NodeState* c : state.consequents) {
    verdicts.push_back(Step(operand, *c, sc, false));
  }
  if (state.wait == 0 && state.remaining > 0) {
    NodeState* c = NewNodeState(operand, sc.arena);
    state.consequents.push_back(c);
    verdicts.push_back(Step(operand, *c, sc, true));
    if (!node->range_unbounded) --state.remaining;
  }
  Tri all = Junction(false, verdicts);
  if (all == Tri::kFalse) return Tri::kFalse;
  return state.remaining == 0 ? all : Tri::kPending;
}

// §16.12.12: what an until's tick says from its operands' verdicts there:
// the until decided true or false, the tick passed on to the next, or not
// yet known. The non-overlapping forms are true at a tick the second operand
// holds at, whatever the first, and the overlapping forms need the first
// there too; a tick the first operand fails at before that fails the until;
// a tick the first holds at with the second false passes on.
enum class UntilTick : uint8_t { kTrue, kFalse, kNext, kPending };

UntilTick TickOfUntil(const PropertyExprNode* node, Tri first, Tri second) {
  bool overlapping = node->range_unbounded;
  if (!overlapping && second == Tri::kTrue) return UntilTick::kTrue;
  if (first == Tri::kFalse) return UntilTick::kFalse;
  if (first == Tri::kPending || second == Tri::kPending) {
    return UntilTick::kPending;
  }
  return second == Tri::kTrue ? UntilTick::kTrue : UntilTick::kNext;
}

// The ticks in order from the first not yet decided, which `wait` indexes;
// an until whose every tick has passed on is not yet decided.
Tri DecideUntil(const PropertyExprNode* node, NodeState& state,
                const std::vector<Tri>& firsts,
                const std::vector<Tri>& seconds) {
  while (state.wait < firsts.size()) {
    switch (TickOfUntil(node, firsts[state.wait], seconds[state.wait])) {
      case UntilTick::kTrue:
        return Tri::kTrue;
      case UntilTick::kFalse:
        return Tri::kFalse;
      case UntilTick::kPending:
        return Tri::kPending;
      case UntilTick::kNext:
        ++state.wait;
        break;
    }
  }
  return Tri::kPending;
}

// One tick of an until: the operands' attempts of the ticks before step on,
// a pair begins at this tick, and the ticks are decided in order.
Tri StepUntil(const PropertyExprNode* node, NodeState& state, StepContext& sc) {
  std::vector<Tri> firsts;
  std::vector<Tri> seconds;
  firsts.reserve(state.consequents.size() + 1);
  seconds.reserve(state.seconds.size() + 1);
  for (size_t i = 0; i < state.consequents.size(); ++i) {
    firsts.push_back(Step(node->operands[0], *state.consequents[i], sc, false));
    seconds.push_back(Step(node->operands[1], *state.seconds[i], sc, false));
  }
  NodeState* first = NewNodeState(node->operands[0], sc.arena);
  NodeState* second = NewNodeState(node->operands[1], sc.arena);
  state.consequents.push_back(first);
  state.seconds.push_back(second);
  firsts.push_back(Step(node->operands[0], *first, sc, true));
  seconds.push_back(Step(node->operands[1], *second, sc, true));
  return DecideUntil(node, state, firsts, seconds);
}

Tri Step(const PropertyExprNode* node, NodeState& state, StepContext& sc,
         bool begin) {
  if (state.verdict != Tri::kPending) return state.verdict;
  switch (node->kind) {
    case PropertyExprNode::Kind::kBoolean:
      state.verdict =
          FromBool(EvalExpr(node->boolean, sc.ctx, sc.arena).IsTruthy());
      break;
    case PropertyExprNode::Kind::kSequence:
      state.verdict = StepSequence(node, state, sc, begin);
      break;
    case PropertyExprNode::Kind::kNot:
      state.verdict =
          Not(Step(node->operands[0], *state.operands[0], sc, begin));
      break;
    case PropertyExprNode::Kind::kOr:
    case PropertyExprNode::Kind::kAnd:
      state.verdict = StepJunction(node, state, sc, begin);
      break;
    case PropertyExprNode::Kind::kIfElse:
      state.verdict = StepIfElse(node, state, sc, begin);
      break;
    case PropertyExprNode::Kind::kImplication:
      state.verdict = StepImplication(node, state, sc, begin);
      break;
    case PropertyExprNode::Kind::kNexttime:
      state.verdict = StepNexttime(node, state, sc, begin);
      break;
    case PropertyExprNode::Kind::kAlways:
      state.verdict = StepAlways(node, state, sc, begin);
      break;
    case PropertyExprNode::Kind::kUntil:
      state.verdict = StepUntil(node, state, sc);
      break;
    case PropertyExprNode::Kind::kImplies:
    case PropertyExprNode::Kind::kIff: {
      Tri first = Step(node->operands[0], *state.operands[0], sc, begin);
      Tri second = Step(node->operands[1], *state.operands[1], sc, begin);
      state.verdict = node->kind == PropertyExprNode::Kind::kImplies
                          ? Implies(first, second)
                          : Iff(first, second);
      break;
    }
  }
  return state.verdict;
}

// The end of the run: a sequence still in flight reads by its strength, an
// antecedent still in flight matches no more, and the rest follows.
Tri Finish(const PropertyExprNode* node, NodeState& state);

Tri FinishJunction(const PropertyExprNode* node, NodeState& state) {
  std::vector<Tri> verdicts;
  verdicts.reserve(node->operands.size());
  for (size_t i = 0; i < node->operands.size(); ++i) {
    verdicts.push_back(Finish(node->operands[i], *state.operands[i]));
  }
  return Junction(node->kind == PropertyExprNode::Kind::kOr, verdicts);
}

Tri FinishIfElse(const PropertyExprNode* node, NodeState& state) {
  Tri then_branch = Finish(node->operands[0], *state.operands[0]);
  Tri else_branch = node->operands.size() > 1
                        ? Finish(node->operands[1], *state.operands[1])
                        : Tri::kTrue;
  return state.condition ? then_branch : else_branch;
}

Tri FinishImplication(const PropertyExprNode* node, NodeState& state) {
  std::vector<Tri> verdicts;
  verdicts.reserve(state.consequents.size());
  for (NodeState* c : state.consequents) {
    verdicts.push_back(Finish(node->operands[0], *c));
  }
  return Junction(false, verdicts);
}

Tri FinishPair(const PropertyExprNode* node, NodeState& state) {
  Tri first = Finish(node->operands[0], *state.operands[0]);
  Tri second = Finish(node->operands[1], *state.operands[1]);
  return node->kind == PropertyExprNode::Kind::kImplies ? Implies(first, second)
                                                        : Iff(first, second);
}

// §16.12.11: the operand attempts begun are finished as themselves; ticks
// of the range the run never reached are no failure of the weak form and
// fail the strong.
Tri FinishAlways(const PropertyExprNode* node, NodeState& state) {
  Tri all = FinishImplication(node, state);
  if (all == Tri::kFalse) return Tri::kFalse;
  if (state.remaining > 0 && node->strong) return Tri::kFalse;
  return all;
}

// §16.12.12: the ticks' operands are finished as themselves and the ticks
// decided in order; an until whose every tick passed on is the weak form
// holding and the strong failing, no tick having the second operand true.
Tri FinishUntil(const PropertyExprNode* node, NodeState& state) {
  std::vector<Tri> firsts;
  std::vector<Tri> seconds;
  firsts.reserve(state.consequents.size());
  seconds.reserve(state.seconds.size());
  for (size_t i = 0; i < state.consequents.size(); ++i) {
    firsts.push_back(Finish(node->operands[0], *state.consequents[i]));
    seconds.push_back(Finish(node->operands[1], *state.seconds[i]));
  }
  Tri decided = DecideUntil(node, state, firsts, seconds);
  if (decided != Tri::kPending) return decided;
  return node->strong ? Tri::kFalse : Tri::kTrue;
}

// §16.12.10: with no further tick the weak form holds and the strong fails;
// an operand begun is finished as itself.
Tri FinishNexttime(const PropertyExprNode* node, NodeState& state) {
  if (state.begun) return Finish(node->operands[0], *state.operands[0]);
  return node->strong ? Tri::kFalse : Tri::kTrue;
}

Tri Finish(const PropertyExprNode* node, NodeState& state) {
  if (state.verdict != Tri::kPending) return state.verdict;
  switch (node->kind) {
    case PropertyExprNode::Kind::kBoolean:
      return Tri::kTrue;
    case PropertyExprNode::Kind::kSequence:
      state.verdict = node->strong ? Tri::kFalse : Tri::kTrue;
      break;
    case PropertyExprNode::Kind::kNot:
      state.verdict = Not(Finish(node->operands[0], *state.operands[0]));
      break;
    case PropertyExprNode::Kind::kOr:
    case PropertyExprNode::Kind::kAnd:
      state.verdict = FinishJunction(node, state);
      break;
    case PropertyExprNode::Kind::kIfElse:
      state.verdict = FinishIfElse(node, state);
      break;
    case PropertyExprNode::Kind::kImplication:
      state.verdict = FinishImplication(node, state);
      break;
    case PropertyExprNode::Kind::kNexttime:
      state.verdict = FinishNexttime(node, state);
      break;
    case PropertyExprNode::Kind::kAlways:
      state.verdict = FinishAlways(node, state);
      break;
    case PropertyExprNode::Kind::kUntil:
      state.verdict = FinishUntil(node, state);
      break;
    case PropertyExprNode::Kind::kImplies:
    case PropertyExprNode::Kind::kIff:
      state.verdict = FinishPair(node, state);
      break;
  }
  return state.verdict;
}

}  // namespace

PropertyTreeState* CreatePropertyTreeState(const PropertyExprNode* root,
                                           SimContext& ctx, Arena& arena) {
  auto* state = arena.Create<PropertyTreeState>();
  state->root = root;
  if (!CollectSequences(root, *state, ctx, arena)) return nullptr;
  return state;
}

std::vector<bool> AdvancePropertyTree(PropertyTreeState& state, bool disabled,
                                      SimContext& ctx, Arena& arena) {
  std::vector<bool> verdicts;
  for (const Expr* site : state.past_sites) EvalExpr(site, ctx, arena);
  if (disabled) {
    state.attempts.clear();
    return verdicts;
  }
  state.attempts.push_back(NewNodeState(state.root, arena));
  StepContext sc{state, ctx, arena};
  std::vector<NodeState*> kept;
  for (size_t i = 0; i < state.attempts.size(); ++i) {
    bool begin = i + 1 == state.attempts.size();
    Tri verdict = Step(state.root, *state.attempts[i], sc, begin);
    if (verdict == Tri::kPending) {
      kept.push_back(state.attempts[i]);
    } else {
      verdicts.push_back(verdict == Tri::kTrue);
    }
  }
  state.attempts = std::move(kept);
  return verdicts;
}

std::vector<bool> FinishPropertyTree(PropertyTreeState& state) {
  std::vector<bool> verdicts;
  verdicts.reserve(state.attempts.size());
  for (NodeState* attempt : state.attempts) {
    verdicts.push_back(Finish(state.root, *attempt) == Tri::kTrue);
  }
  state.attempts.clear();
  return verdicts;
}

}  // namespace delta
