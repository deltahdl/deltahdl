#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiIsExprOperandType(int type) {
  return VpiIsExprType(type) || VpiIsNetsType(type) || VpiIsVariablesType(type);
}

bool VpiIsExprObject(VpiHandle obj) {
  return VpiIsExprType(obj->type) && !obj->written_as_stmt;
}

namespace {

// §37.58 for a bit select, §37.16 and §37.17 detail 13 for a net bit and a var
// bit: the bit's index, and the object it is a bit of.
bool TryResolveBitRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (ref->type != vpiBitSelect && ref->type != vpiNetBit &&
      ref->type != vpiRegBit) {
    return false;
  }
  if (type == vpiIndex) {
    out = ref->index_expr;
    return true;
  }
  if (type != vpiParent) return false;
  out = ref->parent;
  return true;
}

// §37.17 detail 6 and §37.22: a variable's leftmost bounds and a range's
// bounds, recorded where the declaration has them and null where the range is
// empty; and, as §37.41 draws them, the bounds of a function's return range.
bool TryResolveRangeBounds(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiLeftRange && type != vpiRightRange) return false;
  if (ref->type != vpiRange && ref->type != vpiFunction &&
      !VpiIsVariablesType(ref->type)) {
    return false;
  }
  out = type == vpiLeftRange ? ref->left_range : ref->right_range;
  return true;
}

}  // namespace

bool TryResolveSelectRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (TryResolveBitRelation(type, ref, out) ||
      TryResolveRangeBounds(type, ref, out)) {
    return true;
  }
  if (ref->type == vpiPartSelect) {
    if (type == vpiLeftRange) {
      out = ref->left_range;
      return true;
    }
    if (type == vpiRightRange) {
      out = ref->right_range;
      return true;
    }
  } else if (ref->type == vpiIndexedPartSelect) {
    if (type == vpiBaseExpr) {
      out = ref->base_expr;
      return true;
    }
    if (type == vpiWidthExpr) {
      out = ref->width_expr;
      return true;
    }
  } else {
    return false;
  }
  // Both kinds reach the simple expression they select into (§37.59).
  if (type != vpiParent) return false;
  out = ref->parent;
  return true;
}

}  // namespace delta
