#include <algorithm>
#include <cstdint>
#include <optional>

#include "common/types.h"
#include "simulator/variable.h"
#include "simulator/vpi_dynamic_ranges.h"
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

bool VpiIsOperandObject(VpiHandle obj) {
  return VpiIsExprOperandType(obj->type) && !obj->written_as_stmt;
}

bool VpiIsExprObject(VpiHandle obj) {
  return VpiIsExprType(obj->type) && !obj->written_as_stmt;
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
      // An operation's children are its operands and the attributes its
      // operator is written with (§37.83), which are no part of its value.
      return std::ranges::all_of(expr->children, [](VpiObject* child) {
        return !VpiIsOperandObject(child) || VpiIsElaborationConstant(child);
      });
    default:
      return false;
  }
}

namespace {

// §37.58 for a bit select, §37.16 and §37.17 detail 13 for a net bit and a var
// bit: the bit's index, and the object it is a bit of. §37.17 detail 5: a var
// select's own index too, and detail 18 with §37.20: an element's of an array
// var, a memory word's among them, the index that selects it out of its
// array. §37.16 (figure) draws the same vpiIndex from a net in an array net.
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

// §37.17 detail 6 and §37.22: a variable's leftmost bounds and a range's
// bounds, recorded where the declaration has them and null where the range is
// empty; as §37.41 draws them, the bounds of a function's return range; as
// §37.11 draws them, an instance array's; as §37.16 detail 26 does, a net's
// leftmost packed bounds; and, as §37.24 does, the bounds of an interconnect
// array's first dimension.
bool TryResolveRangeBounds(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiLeftRange && type != vpiRightRange) return false;
  if (ref->type != vpiRange && ref->type != vpiFunction &&
      !VpiIsVariablesType(ref->type) && !VpiIsNetsType(ref->type) &&
      !VpiIsInstanceArrayType(ref->type)) {
    return false;
  }
  // §37.22 detail 1: a dynamic array's or queue's, and its first range's,
  // are those of the elements it holds now.
  if (const VpiObject* range = VpiDynamicRangeOf(ref)) {
    out = VpiDynamicRangeBound(type, *range);
    return true;
  }
  out = type == vpiLeftRange ? ref->left_range : ref->right_range;
  return true;
}

// §37.35 (figure): a prim term reaches the expression its terminal connects,
// through the diagram's untagged arrow to `expr`. The expression is the
// term's child of a kind that class holds, a net or variable among them
// (§37.58), never one whose own type is the relation's tag.
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

// §37.17 detail 8: the expression a variable's declaration initializes it
// with; a variable declared with none is left to the relations below.
bool TryResolveVariableInit(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiExpr || VpiVariableInitExpr(ref) == nullptr) return false;
  out = VpiVariableInitExpr(ref);
  return true;
}

// §37.16 (figure) and detail 20: the net a net, a net bit or an array net is
// simulated as, which an implementation that collapses nets across the
// hierarchy (§23.3.3.7) makes one for all of them. The run keeps every net a
// port connects apart, joining them through the port, so each is simulated as
// itself.
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
  // Both kinds reach the simple expression they select into (§37.59).
  if (type != vpiParent) return false;
  out = ref->parent;
  return true;
}

}  // namespace delta
