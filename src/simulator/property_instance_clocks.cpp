#include "simulator/property_instance_clocks.h"

#include <vector>

#include "common/arena.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"
#include "simulator/property_attempts.h"
#include "simulator/property_clocks.h"
#include "simulator/sequence_flatten.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

// §16.12.17: a property may instantiate itself, so the walk into the bodies
// of instances stops at this depth.
constexpr int kMaxInstanceDepth = 4;

// What the walk numbers clocks into and runs in.
struct ClockWalk {
  PropertyClocks& clocks;
  SimContext& ctx;
  Arena& arena;
};

void Number(const ClockWalk& w, const std::vector<EventExpr>& clock) {
  if (!clock.empty()) ClockIndexOf(w.clocks, clock);
}

// §16.13.1 and §16.13.3: the clocks a sequence of an instantiated body names,
// its declared clock, the clock at its end and those before its operands, as
// the flattening of the sequence with the actuals substituted gives them.
void NumberSequenceClocks(const ModuleItem* seq, const ActualsByFormal& actuals,
                          const ClockWalk& w) {
  LinearSequence flat;
  if (!FlattenLinearSequence(seq, w.ctx, w.arena, flat)) return;
  if (!actuals.empty()) {
    flat = SubstituteLinearSequence(flat, actuals, w.ctx, w.arena);
  }
  Number(w, flat.declared_clock);
  Number(w, flat.clock_out);
  for (const std::vector<EventExpr>& clock : flat.operand_clocks) {
    Number(w, clock);
  }
}

void WalkNode(const PropertyExprNode* node, const ActualsByFormal& actuals,
              bool in_body, const ClockWalk& w, int depth);

// §16.12.17: the instance a boolean operand is, where it instantiates a named
// property: the property's clock and the clocks of its body, the actuals of
// the instance, themselves over the enclosing body's actuals, in its formals'
// places.
void WalkInstance(const Expr* boolean, const ActualsByFormal& actuals,
                  const ClockWalk& w, int depth) {
  if (depth >= kMaxInstanceDepth) return;
  Expr* instance = SubstituteFormals(boolean, actuals, w.arena);
  const ModuleItem* decl = InstantiatedProperty(instance, w.ctx);
  if (decl == nullptr) return;
  ActualsByFormal inner = BindInstanceActuals(decl, instance, w.arena);
  Number(w, SubstituteClock(decl->prop_clock, inner, w.arena));
  WalkNode(decl->prop_body_tree, inner, true, w, depth + 1);
}

// The nodes of a tree; `in_body` says the tree is an instantiated body, whose
// own clocks are numbered, the assertion's own tree having been numbered as
// its sequences were collected.
void WalkNode(const PropertyExprNode* node, const ActualsByFormal& actuals,
              bool in_body, const ClockWalk& w, int depth) {
  if (node == nullptr) return;
  if (in_body) {
    Number(w, SubstituteClock(node->clock, actuals, w.arena));
    if (node->sequence != nullptr) {
      NumberSequenceClocks(node->sequence, actuals, w);
    }
  }
  if (node->boolean != nullptr) WalkInstance(node->boolean, actuals, w, depth);
  for (const PropertyExprNode* operand : node->operands) {
    WalkNode(operand, actuals, in_body, w, depth);
  }
}

}  // namespace

void RegisterInstanceBodyClocks(const PropertyExprNode* root,
                                PropertyClocks& clocks, SimContext& ctx,
                                Arena& arena) {
  WalkNode(root, ActualsByFormal{}, false, ClockWalk{clocks, ctx, arena}, 0);
}

}  // namespace delta
