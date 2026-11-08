#include <cstddef>
#include <cstdint>
#include <vector>

#include "parser/ast_stmt.h"
#include "simulator/property_attempts.h"
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

Tri Junction(bool is_or, const std::vector<Tri>& verdicts) {
  Tri decisive = is_or ? Tri::kTrue : Tri::kFalse;
  Tri result = is_or ? Tri::kFalse : Tri::kTrue;
  for (Tri t : verdicts) {
    if (t == decisive) result = decisive;
    if (t == Tri::kPending && result != decisive) result = Tri::kPending;
  }
  return result;
}

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

Tri FinishNexttime(const PropertyExprNode* node, NodeState& state) {
  if (state.begun) return Finish(node->operands[0], *state.operands[0]);
  return node->strong ? Tri::kFalse : Tri::kTrue;
}

}  // namespace

Tri Finish(const PropertyExprNode* node, NodeState& state) {
  if (state.verdict != Tri::kPending) return state.verdict;
  switch (node->kind) {
    case PropertyExprNode::Kind::kBoolean:
      if (state.expansion == nullptr) return Tri::kTrue;
      state.verdict = Finish(state.expansion, *state.operands[0]);
      break;
    case PropertyExprNode::Kind::kSequence:
      state.verdict = state.strong ? Tri::kFalse : Tri::kTrue;
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

PropertyVerdict VerdictOf(const PropertyExprNode* root,
                          const NodeState& state) {
  PropertyVerdict verdict;
  verdict.holds = state.verdict == Tri::kTrue;
  verdict.vacuous = verdict.holds && !Nonvacuous(root, state);
  verdict.bindings = state.bindings;
  verdict.started = state.started;
  return verdict;
}

void ReadPlainSequencesAsStrong(PropertyTreeState& state) {
  state.plain_sequences_strong = true;
}

std::vector<PropertyVerdict> FinishPropertyTree(PropertyTreeState& state) {
  std::vector<PropertyVerdict> verdicts;
  verdicts.reserve(state.attempts.size());
  for (NodeState* attempt : state.attempts) {
    Finish(state.root, *attempt);
    verdicts.push_back(VerdictOf(state.root, *attempt));
  }
  state.attempts.clear();
  return verdicts;
}

std::size_t AbortPropertyTreeAttempts(PropertyTreeState& state) {
  const std::size_t kAborted = state.attempts.size();
  state.attempts.clear();
  return kAborted;
}

std::size_t AbortPropertyTreeAttemptAt(PropertyTreeState& state,
                                       uint64_t started) {
  return std::erase_if(state.attempts, [started](const NodeState* attempt) {
    return attempt->started == started;
  });
}

}  // namespace delta
