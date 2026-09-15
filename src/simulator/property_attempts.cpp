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

// One operand of the tree: a boolean or a sequence, the sequence flattened
// once for every attempt.
struct Leaf {
  const PropertyExprNode* node;
  LinearSequence body;
};

// The operands' states of one attempt, parallel to the leaves: a decided
// operand's verdict, and a sequence operand's attempt while it is in flight.
struct LeafState {
  Tri verdict = Tri::kPending;
  LinearSequenceAttempt* attempt = nullptr;
};

struct TreeAttempt {
  std::vector<LeafState> leaves;
};

}  // namespace

struct PropertyTreeState {
  const PropertyExprNode* root = nullptr;
  std::vector<Leaf> leaves;
  std::vector<const Expr*> past_sites;
  std::vector<TreeAttempt> attempts;
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

// The leaves of the tree in the order the evaluation reads them, each
// sequence flattened; answers false where a sequence is not readable.
bool CollectLeaves(const PropertyExprNode* node, PropertyTreeState& state,
                   SimContext& ctx, Arena& arena) {
  switch (node->kind) {
    case PropertyExprNode::Kind::kBoolean:
      state.leaves.push_back({node, LinearSequence{}});
      CollectPastDirectedSites(node->boolean, state.past_sites);
      return true;
    case PropertyExprNode::Kind::kIfElse:
      // §16.12.6: the condition is read at the attempt's tick as a boolean
      // operand is, its leaf standing before the branches'.
      state.leaves.push_back({node, LinearSequence{}});
      CollectPastDirectedSites(node->boolean, state.past_sites);
      for (const PropertyExprNode* operand : node->operands) {
        if (!CollectLeaves(operand, state, ctx, arena)) return false;
      }
      return true;
    case PropertyExprNode::Kind::kSequence: {
      Leaf leaf{node, LinearSequence{}};
      if (!FlattenLinearSequence(node->sequence, ctx, arena, leaf.body)) {
        return false;
      }
      ForEachLinearSequenceExpr(leaf.body, [&state](const Expr* e) {
        CollectPastDirectedSites(e, state.past_sites);
      });
      state.leaves.push_back(std::move(leaf));
      return true;
    }
    default:
      for (const PropertyExprNode* operand : node->operands) {
        if (!CollectLeaves(operand, state, ctx, arena)) return false;
      }
      return true;
  }
}

Tri Not(Tri t) {
  if (t == Tri::kPending) return t;
  return t == Tri::kTrue ? Tri::kFalse : Tri::kTrue;
}

// §16.12.3 to §16.12.6 over the operands' verdicts: not inverts a decided
// operand; or is true where any operand is and false where every one is;
// and is false where any operand is and true where every one is; if-else
// is the branch its condition selects; else the tree is not yet decided.
// `next` walks the leaves in the order they were collected.
Tri Evaluate(const PropertyExprNode* node, const TreeAttempt& attempt,
             size_t& next) {
  switch (node->kind) {
    case PropertyExprNode::Kind::kBoolean:
    case PropertyExprNode::Kind::kSequence:
      return attempt.leaves[next++].verdict;
    case PropertyExprNode::Kind::kNot:
      return Not(Evaluate(node->operands[0], attempt, next));
    case PropertyExprNode::Kind::kIfElse: {
      // §16.12.6: with the condition true the property is the then branch;
      // with it false, the else branch, or true where none was written.
      // Both branches are walked so that `next` passes their leaves.
      Tri condition = attempt.leaves[next++].verdict;
      Tri then_branch = Evaluate(node->operands[0], attempt, next);
      Tri else_branch = node->operands.size() > 1
                            ? Evaluate(node->operands[1], attempt, next)
                            : Tri::kTrue;
      return condition == Tri::kTrue ? then_branch : else_branch;
    }
    case PropertyExprNode::Kind::kOr:
    case PropertyExprNode::Kind::kAnd: {
      bool is_or = node->kind == PropertyExprNode::Kind::kOr;
      Tri decisive = is_or ? Tri::kTrue : Tri::kFalse;
      Tri result = is_or ? Tri::kFalse : Tri::kTrue;
      for (const PropertyExprNode* operand : node->operands) {
        Tri t = Evaluate(operand, attempt, next);
        if (t == decisive) result = decisive;
        if (t == Tri::kPending && result != decisive) result = Tri::kPending;
      }
      return result;
    }
  }
  return Tri::kPending;
}

Tri FromStep(SequenceStep step) {
  if (step == SequenceStep::kMatched) return Tri::kTrue;
  if (step == SequenceStep::kFailed) return Tri::kFalse;
  return Tri::kPending;
}

// One tick of one attempt's operands: a boolean is read at the tick the
// attempt begins at, and a sequence's attempt is stepped while it is in
// flight.
void StepLeaves(PropertyTreeState& state, TreeAttempt& attempt, bool begin,
                SimContext& ctx, Arena& arena) {
  for (size_t i = 0; i < state.leaves.size(); ++i) {
    const Leaf& leaf = state.leaves[i];
    LeafState& ls = attempt.leaves[i];
    if (ls.verdict != Tri::kPending) continue;
    if (leaf.node->kind == PropertyExprNode::Kind::kBoolean ||
        leaf.node->kind == PropertyExprNode::Kind::kIfElse) {
      ls.verdict = EvalExpr(leaf.node->boolean, ctx, arena).IsTruthy()
                       ? Tri::kTrue
                       : Tri::kFalse;
      continue;
    }
    if (begin) ls.attempt = NewSequenceAttempt(leaf.body, arena);
    ls.verdict = FromStep(
        StepSequenceAttempt(leaf.body, *ls.attempt, begin, ctx, arena));
  }
}

}  // namespace

PropertyTreeState* CreatePropertyTreeState(const PropertyExprNode* root,
                                           SimContext& ctx, Arena& arena) {
  auto* state = arena.Create<PropertyTreeState>();
  state->root = root;
  if (!CollectLeaves(root, *state, ctx, arena)) return nullptr;
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
  state.attempts.push_back(
      TreeAttempt{std::vector<LeafState>(state.leaves.size())});
  std::vector<TreeAttempt> kept;
  for (size_t i = 0; i < state.attempts.size(); ++i) {
    bool begin = i + 1 == state.attempts.size();
    StepLeaves(state, state.attempts[i], begin, ctx, arena);
    size_t next = 0;
    Tri verdict = Evaluate(state.root, state.attempts[i], next);
    if (verdict == Tri::kPending) {
      kept.push_back(std::move(state.attempts[i]));
    } else {
      verdicts.push_back(verdict == Tri::kTrue);
    }
  }
  state.attempts = std::move(kept);
  return verdicts;
}

std::vector<bool> FinishPropertyTree(PropertyTreeState& state) {
  std::vector<bool> verdicts;
  for (TreeAttempt& attempt : state.attempts) {
    for (size_t i = 0; i < state.leaves.size(); ++i) {
      LeafState& ls = attempt.leaves[i];
      if (ls.verdict != Tri::kPending) continue;
      ls.verdict = state.leaves[i].node->strong ? Tri::kFalse : Tri::kTrue;
    }
    size_t next = 0;
    verdicts.push_back(Evaluate(state.root, attempt, next) == Tri::kTrue);
  }
  state.attempts.clear();
  return verdicts;
}

}  // namespace delta
