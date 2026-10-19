#include "simulator/vpi_constraint_relations.h"

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

const std::vector<VpiObject*>* VpiConstraintListOf(int type,
                                                   const VpiObject* ref) {
  if (type == vpiElseConst && ref->type == vpiConstrIfElse) {
    return &ref->else_constraint_exprs;
  }
  if (ref->type != vpiConstraintOrdering) return nullptr;
  if (type == vpiSolveBefore) return &ref->solve_before;
  return type == vpiSolveAfter ? &ref->solve_after : nullptr;
}

namespace {

// The expression a distribution weights, its one child no dist item, or the
// one a soft disable discards the soft constraints of, its one child.
VpiObject* ConstraintItemExpr(const VpiObject* ref) {
  VpiObject* expr = nullptr;
  for (VpiObject* child : ref->children) {
    if (child->type != vpiDistItem) expr = child;
  }
  return expr;
}

}  // namespace

bool VpiTryResolveConstraintRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type == vpiParent && ref->type == vpiConstraint) {
    const bool kOfObject =
        ref->parent != nullptr && ref->parent->type == vpiClassObj;
    out = kOfObject ? ref->parent : nullptr;
    return true;
  }
  if (type == vpiExpr &&
      (ref->type == vpiDistribution || ref->type == vpiSoftDisable)) {
    out = ConstraintItemExpr(ref);
    return true;
  }
  if (ref->type != vpiDistItem) return false;
  if (type == vpiValueRange) {
    out = ref->value_range;
    return true;
  }
  if (type == vpiWeight) {
    out = ref->weight;
    return true;
  }
  return false;
}

}  // namespace delta
