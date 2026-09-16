#include <cstddef>
#include <cstdint>
#include <vector>

#include "parser/ast_stmt.h"
#include "simulator/property_attempts_internal.h"
#include "simulator/sequence_monitor.h"

namespace delta {

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

namespace {

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

}  // namespace

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

namespace {

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

// §16.12.16: the item selected is finished as itself; none selected, the
// case holds.
Tri FinishCase(const PropertyExprNode* node, NodeState& state) {
  if (state.selected == node->operands.size()) return Tri::kTrue;
  return Finish(node->operands[state.selected],
                *state.operands[state.selected]);
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

// §16.12.11 and §16.12.13: the operand attempts begun are finished as
// themselves; ticks of the range the run never reached are no failure of
// the weak forms and fail the strong, an eventually with a true operand
// holding either way.
Tri FinishAlways(const PropertyExprNode* node, NodeState& state) {
  bool eventually = node->kind == PropertyExprNode::Kind::kEventually;
  std::vector<Tri> verdicts;
  verdicts.reserve(state.consequents.size());
  for (NodeState* c : state.consequents) {
    verdicts.push_back(Finish(node->operands[0], *c));
  }
  Tri joined = Junction(eventually, verdicts);
  Tri decisive = eventually ? Tri::kTrue : Tri::kFalse;
  if (joined == decisive) return decisive;
  if (state.remaining > 0) return node->strong ? Tri::kFalse : Tri::kTrue;
  return joined;
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

}  // namespace

Tri Finish(const PropertyExprNode* node, NodeState& state) {
  if (state.verdict != Tri::kPending) return state.verdict;
  switch (node->kind) {
    case PropertyExprNode::Kind::kBoolean:
      // §16.12.17: an instance expanded is finished as its body; a boolean
      // never stepped was never required.
      if (state.expansion == nullptr) return Tri::kTrue;
      state.verdict = Finish(state.expansion, *state.operands[0]);
      break;
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
    case PropertyExprNode::Kind::kEventually:
      state.verdict = FinishAlways(node, state);
      break;
    case PropertyExprNode::Kind::kUntil:
      state.verdict = FinishUntil(node, state);
      break;
    case PropertyExprNode::Kind::kAbort:
      // §16.12.14: an abort marked between the last tick and the end takes
      // precedence; otherwise the property is its operand.
      state.verdict = state.aborted
                          ? (node->accept ? Tri::kTrue : Tri::kFalse)
                          : Finish(node->operands[0], *state.operands[0]);
      break;
    case PropertyExprNode::Kind::kCase:
      state.verdict = FinishCase(node, state);
      break;
    case PropertyExprNode::Kind::kImplies:
    case PropertyExprNode::Kind::kIff:
      state.verdict = FinishPair(node, state);
      break;
  }
  return state.verdict;
}

}  // namespace delta
