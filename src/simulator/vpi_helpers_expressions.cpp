#include <algorithm>
#include <cstdint>
#include <optional>

#include "common/types.h"
#include "simulator/variable.h"
#include "simulator/vpi_dynamic_ranges.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiIsExprOperandType(int type) {
  return VpiIsExprType(type) || VpiIsNetsType(type) || VpiIsVariablesType(type);
}

bool VpiIsOperandObject(VpiHandle obj) {
  return VpiIsExprOperandType(obj->type) && !obj->written_as_stmt;
}

std::optional<int64_t> VpiElaborationValue(const VpiObject* expr) {
  if (expr == nullptr || expr->var == nullptr) return std::nullopt;
  switch (expr->type) {
    case vpiConstant:
    case vpiParameter:
    case vpiSpecParam:
      return static_cast<int64_t>(expr->var->value.ToUint64());
    default:
      return std::nullopt;
  }
}

bool VpiIsElaborationConstant(const VpiObject* expr) {
  if (expr == nullptr) return false;
  switch (expr->type) {
    case vpiConstant:
    case vpiParameter:
    case vpiSpecParam:
      return true;
    case vpiOperation:
      return std::ranges::all_of(expr->children, [](VpiObject* child) {
        return !VpiIsOperandObject(child) || VpiIsElaborationConstant(child);
      });
    default:
      return false;
  }
}

namespace {

bool TryResolveBitRelation(int type, VpiHandle ref, VpiHandle& out) {
  const bool kElement = ref->array_member && (VpiIsVariablesType(ref->type) ||
                                              VpiIsNetsType(ref->type));
  if ((ref->type == vpiVarSelect || kElement) && type == vpiIndex) {
    out = ref->index_expr;
    return true;
  }
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

bool TryResolveRangeBounds(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiLeftRange && type != vpiRightRange) return false;
  if (ref->type != vpiRange && ref->type != vpiFunction &&
      !VpiIsVariablesType(ref->type) && !VpiIsNetsType(ref->type) &&
      !VpiIsInstanceArrayType(ref->type)) {
    return false;
  }
  if (const VpiObject* range = VpiDynamicRangeOf(ref)) {
    out = VpiDynamicRangeBound(type, *range);
    return true;
  }
  out = type == vpiLeftRange ? ref->left_range : ref->right_range;
  return true;
}

bool TryResolvePrimTermExpr(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiExpr || ref->type != vpiPrimTerm) return false;
  out = nullptr;
  for (VpiObject* child : ref->children) {
    if (VpiIsOperandObject(child)) {
      out = child;
      break;
    }
  }
  return true;
}

bool TryResolveVariableInit(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiExpr || VpiVariableInitExpr(ref) == nullptr) return false;
  out = VpiVariableInitExpr(ref);
  return true;
}

bool TryResolveSimNet(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiSimNet || !VpiIsNetsType(ref->type)) return false;
  out = ref;
  return true;
}

}  // namespace

bool TryResolveSelectRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (TryResolveBitRelation(type, ref, out) ||
      TryResolveSimNet(type, ref, out) ||
      TryResolveRangeBounds(type, ref, out) ||
      TryResolvePrimTermExpr(type, ref, out) ||
      TryResolveVariableInit(type, ref, out)) {
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
  if (type != vpiParent) return false;
  out = ref->parent;
  return true;
}

}  // namespace delta
