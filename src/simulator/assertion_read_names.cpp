#include "simulator/assertion_read_names.h"

#include <string>
#include <unordered_set>

#include "common/arena.h"
#include "elaborator/sensitivity.h"
#include "parser/ast.h"
#include "simulator/expr_walk.h"
#include "simulator/property_attempts.h"
#include "simulator/sequence_flatten.h"

namespace delta {

namespace {

// The dotted spelling of a hierarchical reference, appended to `out`, and
// whether `e` is one. §23.6 writes a name that crosses an instance boundary as
// `u.req`, and the child instance's variable is keyed under exactly that
// spelling, so the whole reference is the name to look up rather than the
// identifiers it is built from. Anything else the walk meets -- a select, a
// call, a class scope resolution -- names no variable of its own, and is
// reported false rather than half a name.
bool AppendHierarchicalName(const Expr* e, std::string& out) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) {
    out += e->text;
    return true;
  }
  if (e->kind != ExprKind::kMemberAccess || e->is_scope_resolution) {
    return false;
  }
  if (!AppendHierarchicalName(e->lhs, out)) return false;
  out += '.';
  return AppendHierarchicalName(e->rhs, out);
}

// The walk over a tree, `depth` counting the instantiated bodies entered.
void CollectTreeReadNames(const PropertyExprNode* node, SimContext& ctx,
                          Arena& arena, std::unordered_set<std::string>& names,
                          int depth) {
  if (node->boolean != nullptr) {
    CollectSampledOperandNames(node->boolean, names);
  }
  const ModuleItem* decl = InstantiatedProperty(node->boolean, ctx);
  if (decl != nullptr && depth < 4) {
    CollectTreeReadNames(decl->prop_body_tree, ctx, arena, names, depth + 1);
  }
  ForEachPropertyActual(node->boolean, [&ctx, &arena, &names,
                                        depth](const PropertyExprNode* actual) {
    CollectTreeReadNames(actual, ctx, arena, names, depth);
  });
  if (node->sequence != nullptr) {
    CollectSequenceReadNames(node->sequence, ctx, arena, names);
  }
  for (const PropertyExprNode* operand : node->operands) {
    CollectTreeReadNames(operand, ctx, arena, names, depth);
  }
}

}  // namespace

// CollectExprReads is the reader-name walk §9.2.2.2.1's implicit sensitivity
// list is built from, which reaches the base and index of a select, the
// arguments of a call and the operands of every subexpression; a
// hierarchical reference is added to what it answers, because it holds
// `u.req` as a member access over two identifiers and so contributes `u` and
// `req`, neither of which is the name the child's variable is keyed under.
void CollectSampledOperandNames(const Expr* e,
                                std::unordered_set<std::string>& out) {
  CollectExprReads(e, out);
  ForEachSubExpr(e, [&out](const Expr* sub) {
    if (sub->kind != ExprKind::kMemberAccess) return;
    std::string name;
    if (AppendHierarchicalName(sub, name)) out.insert(name);
  });
}

void CollectSequenceReadNames(const ModuleItem* seq, SimContext& ctx,
                              Arena& arena,
                              std::unordered_set<std::string>& names) {
  LinearSequence flat;
  if (!FlattenLinearSequence(seq, ctx, arena, flat)) return;
  ForEachLinearSequenceExpr(
      flat, [&names](const Expr* e) { CollectSampledOperandNames(e, names); });
}

void CollectPropertyTreeReadNames(const PropertyExprNode* node, SimContext& ctx,
                                  Arena& arena,
                                  std::unordered_set<std::string>& names) {
  CollectTreeReadNames(node, ctx, arena, names, 0);
}

}  // namespace delta
