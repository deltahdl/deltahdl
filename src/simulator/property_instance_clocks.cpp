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

constexpr int kMaxInstanceDepth = 4;

struct ClockWalk {
  PropertyClocks& clocks;
  SimContext& ctx;
  Arena& arena;
};

void Number(const ClockWalk& w, const std::vector<EventExpr>& clock) {
  if (!clock.empty()) ClockIndexOf(w.clocks, clock);
}

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
