#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiIsExprOperandType(int type) {
  return VpiIsExprType(type) || VpiIsNetsType(type) || VpiIsVariablesType(type);
}

bool TryResolveSelectRelation(int type, VpiHandle ref, VpiHandle& out) {
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
