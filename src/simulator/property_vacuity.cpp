#include <algorithm>
#include <cstddef>
#include <vector>

#include "parser/ast_stmt.h"
#include "simulator/property_attempts_internal.h"

// §16.14.8: an evaluation attempt of a property is either vacuous or
// nonvacuous, and a vacuous success on every attempt may mark a problem in
// the design or in the property, so the attempts decided true are told
// apart by the structure of the property, as the clause defines
// nonvacuity, over the states the attempt kept.

namespace delta {

namespace {

// §16.14.8 (e), (f) and (aa): an or, an and or an iff is nonvacuous where
// either operand's attempt is.
bool AnyOperandNonvacuous(const PropertyExprNode* node,
                          const NodeState& state) {
  for (size_t i = 0; i < node->operands.size() && i < state.operands.size();
       ++i) {
    if (Nonvacuous(node->operands[i], *state.operands[i])) return true;
  }
  return false;
}

// §16.14.8 (g): an if is nonvacuous where its condition held and the then
// branch's attempt is nonvacuous, or where its condition did not hold and
// the else branch's is; without an else, a condition that did not hold
// makes the attempt vacuous.
bool NonvacuousIfElse(const PropertyExprNode* node, const NodeState& state) {
  size_t branch = state.condition ? 0 : 1;
  if (branch >= node->operands.size() || branch >= state.operands.size()) {
    return false;
  }
  return Nonvacuous(node->operands[branch], *state.operands[branch]);
}

// §16.14.8 (p) to (r): an always is nonvacuous where a tick's attempt of
// its operand is and the operand failed at no tick before; (s) to (u): an
// eventually where a tick's attempt is and the operand held at no tick
// before.
bool NonvacuousAlways(const PropertyExprNode* node, const NodeState& state) {
  Tri ending = node->kind == PropertyExprNode::Kind::kEventually ? Tri::kTrue
                                                                 : Tri::kFalse;
  for (const NodeState* tick : state.consequents) {
    if (Nonvacuous(node->operands[0], *tick)) return true;
    if (tick->verdict == ending) return false;
  }
  return false;
}

// §16.14.8 (v) to (y): an until is nonvacuous where, at a tick, the first
// operand's attempt is nonvacuous or, for the forms other than until_with
// and s_until_with, the second's is, the second operand holding at no tick
// before and the first at every tick before.
bool NonvacuousUntil(const PropertyExprNode* node, const NodeState& state) {
  bool with = node->range_unbounded;
  size_t ticks = std::min(state.consequents.size(), state.seconds.size());
  for (size_t i = 0; i < ticks; ++i) {
    const NodeState& first = *state.consequents[i];
    const NodeState& second = *state.seconds[i];
    if (Nonvacuous(node->operands[0], first)) return true;
    if (!with && Nonvacuous(node->operands[1], second)) return true;
    if (second.verdict == Tri::kTrue || first.verdict != Tri::kTrue) {
      return false;
    }
  }
  return false;
}

// §16.14.8 (h), (j) and (k): an implication or a followed-by is nonvacuous
// where a consequent begun at an end point of the antecedent is.
bool NonvacuousImplication(const PropertyExprNode* node,
                           const NodeState& state) {
  for (const NodeState* consequent : state.consequents) {
    if (Nonvacuous(node->operands[0], *consequent)) return true;
  }
  return false;
}

// §16.14.8 (af): a case is nonvacuous as the item it selected, the default
// among them, and vacuous where it selected none.
bool NonvacuousCase(const PropertyExprNode* node, const NodeState& state) {
  if (state.selected >= node->operands.size() ||
      state.selected >= state.operands.size()) {
    return false;
  }
  return Nonvacuous(node->operands[state.selected],
                    *state.operands[state.selected]);
}

// The one operand's attempt, where the node begun one.
bool NonvacuousOperand(const PropertyExprNode* node, const NodeState& state) {
  if (node->operands.empty() || state.operands.empty()) return false;
  return Nonvacuous(node->operands[0], *state.operands[0]);
}

}  // namespace

bool Nonvacuous(const PropertyExprNode* node, const NodeState& state) {
  switch (node->kind) {
    case PropertyExprNode::Kind::kBoolean:
      // §16.14.8 (i): an instance as the body it expanded to; (a): a boolean
      // is a sequence of one tick.
      if (state.expansion == nullptr) return true;
      return state.operands.empty() ||
             Nonvacuous(state.expansion, *state.operands[0]);
    case PropertyExprNode::Kind::kSequence:
      return true;
    case PropertyExprNode::Kind::kNot:
      return NonvacuousOperand(node, state);
    case PropertyExprNode::Kind::kOr:
    case PropertyExprNode::Kind::kAnd:
    case PropertyExprNode::Kind::kIff:
      return AnyOperandNonvacuous(node, state);
    case PropertyExprNode::Kind::kIfElse:
      return NonvacuousIfElse(node, state);
    case PropertyExprNode::Kind::kImplication:
      return NonvacuousImplication(node, state);
    case PropertyExprNode::Kind::kImplies:
      // §16.14.8 (z): the first operand held and the second's attempt is
      // nonvacuous.
      return state.operands.size() > 1 &&
             state.operands[0]->verdict == Tri::kTrue &&
             Nonvacuous(node->operands[1], *state.operands[1]);
    case PropertyExprNode::Kind::kNexttime:
      // §16.14.8 (l) to (o): there was a next clock event and the attempt
      // begun there is nonvacuous.
      return state.begun && NonvacuousOperand(node, state);
    case PropertyExprNode::Kind::kAlways:
    case PropertyExprNode::Kind::kEventually:
      return NonvacuousAlways(node, state);
    case PropertyExprNode::Kind::kUntil:
      return NonvacuousUntil(node, state);
    case PropertyExprNode::Kind::kAbort:
      // §16.14.8 (ab) to (ae): the condition held at no step of the attempt
      // and the operand's attempt is nonvacuous.
      return !state.aborted && NonvacuousOperand(node, state);
    case PropertyExprNode::Kind::kCase:
      return NonvacuousCase(node, state);
  }
  return false;
}

}  // namespace delta
