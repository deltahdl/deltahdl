#include <algorithm>
#include <cstddef>
#include <vector>

#include "parser/ast_stmt.h"
#include "simulator/property_attempts_internal.h"

namespace delta {

namespace {

bool AnyOperandNonvacuous(const PropertyExprNode* node,
                          const NodeState& state) {
  for (size_t i = 0; i < node->operands.size() && i < state.operands.size();
       ++i) {
    if (Nonvacuous(node->operands[i], *state.operands[i])) return true;
  }
  return false;
}

bool NonvacuousIfElse(const PropertyExprNode* node, const NodeState& state) {
  size_t branch = state.condition ? 0 : 1;
  if (branch >= node->operands.size() || branch >= state.operands.size()) {
    return false;
  }
  return Nonvacuous(node->operands[branch], *state.operands[branch]);
}

bool NonvacuousAlways(const PropertyExprNode* node, const NodeState& state) {
  Tri ending = node->kind == PropertyExprNode::Kind::kEventually ? Tri::kTrue
                                                                 : Tri::kFalse;
  for (const NodeState* tick : state.consequents) {
    if (Nonvacuous(node->operands[0], *tick)) return true;
    if (tick->verdict == ending) return false;
  }
  return false;
}

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

bool NonvacuousImplication(const PropertyExprNode* node,
                           const NodeState& state) {
  for (const NodeState* consequent : state.consequents) {
    if (Nonvacuous(node->operands[0], *consequent)) return true;
  }
  return false;
}

bool NonvacuousCase(const PropertyExprNode* node, const NodeState& state) {
  if (state.selected >= node->operands.size() ||
      state.selected >= state.operands.size()) {
    return false;
  }
  return Nonvacuous(node->operands[state.selected],
                    *state.operands[state.selected]);
}

bool NonvacuousOperand(const PropertyExprNode* node, const NodeState& state) {
  if (node->operands.empty() || state.operands.empty()) return false;
  return Nonvacuous(node->operands[0], *state.operands[0]);
}

}  // namespace

bool Nonvacuous(const PropertyExprNode* node, const NodeState& state) {
  switch (node->kind) {
    case PropertyExprNode::Kind::kBoolean:
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
      return state.operands.size() > 1 &&
             state.operands[0]->verdict == Tri::kTrue &&
             Nonvacuous(node->operands[1], *state.operands[1]);
    case PropertyExprNode::Kind::kNexttime:
      return state.begun && NonvacuousOperand(node, state);
    case PropertyExprNode::Kind::kAlways:
    case PropertyExprNode::Kind::kEventually:
      return NonvacuousAlways(node, state);
    case PropertyExprNode::Kind::kUntil:
      return NonvacuousUntil(node, state);
    case PropertyExprNode::Kind::kAbort:
      return !state.aborted && NonvacuousOperand(node, state);
    case PropertyExprNode::Kind::kCase:
      return NonvacuousCase(node, state);
  }
  return false;
}

}  // namespace delta
