#include <cstddef>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiIsTypespecType(int type) {
  switch (type) {
    case vpiTypespec:
    case vpiTypeParameter:
    case vpiLongIntTypespec:
    case vpiShortIntTypespec:
    case vpiIntTypespec:
    case vpiIntegerTypespec:
    case vpiTimeTypespec:
    case vpiRealTypespec:
    case vpiShortRealTypespec:
    case vpiByteTypespec:
    case vpiClassTypespec:
    case vpiStringTypespec:
    case vpiChandleTypespec:
    case vpiEnumTypespec:
    case vpiStructTypespec:
    case vpiUnionTypespec:
    case vpiBitTypespec:
    case vpiLogicTypespec:
    case vpiPackedArrayTypespec:
    case vpiArrayTypespec:
    case vpiVoidTypespec:
    case vpiSequenceTypespec:
    case vpiPropertyTypespec:
    case vpiEventTypespec:
    case vpiInterfaceTypespec:
      return true;
    default:
      return false;
  }
}

const char* VpiTypespecName(int ts_type, bool denotes_user_typedef,
                            const char* typedef_name, const char* class_name) {
  if (ts_type == vpiClassTypespec) return class_name;
  if (denotes_user_typedef) return typedef_name;
  return nullptr;
}

VpiHandle VpiTypespecTypedefAlias(bool is_alias, VpiHandle aliased_typedef) {
  return is_alias ? aliased_typedef : nullptr;
}

VpiHandle VpiTypespecIndexTypespec(bool is_assoc_array_typespec,
                                   bool wildcard_index,
                                   VpiHandle key_typespec) {
  if (!is_assoc_array_typespec || wildcard_index) return nullptr;
  return key_typespec;
}

std::vector<VpiHandle> VpiTypespecMembers(
    int ts_type, const std::vector<VpiHandle>& members) {
  if (ts_type == vpiStructTypespec || ts_type == vpiUnionTypespec) {
    return members;
  }
  return {};
}

VpiHandle VpiTypespecChild(VpiHandle obj) {
  if (!obj) return nullptr;
  for (auto* child : obj->children) {
    if (VpiIsTypespecType(child->type)) return child;
  }
  return nullptr;
}

const char* VpiTypespecMemberName(VpiHandle member) {
  if (!member) return nullptr;
  return member->name.data();
}

VpiHandle VpiTypespecMemberDefaultExpr(VpiHandle member) {
  if (!member) return nullptr;
  for (auto* child : member->children) {
    if (VpiIsExprType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiTypespecElemTypespec(bool has_ranges, VpiHandle element_typespec) {
  return has_ranges ? element_typespec : nullptr;
}

std::vector<VpiRangeDesc> VpiTypespecRanges(
    const std::vector<VpiArrayDimension>& dims) {
  std::vector<VpiRangeDesc> ranges;
  for (const auto& dim : dims) {
    if (dim.implicit_element_range) continue;
    VpiRangeDesc range;
    range.empty = VpiDimensionRangeIsEmpty(dim.kind);
    range.left_expr = dim.left_expr;
    range.right_expr = dim.right_expr;
    range.size = dim.size;
    ranges.push_back(range);
  }
  return ranges;
}

static VpiRangeDesc LeftmostTypespecRange(
    const std::vector<VpiArrayDimension>& dims) {
  for (const auto& dim : dims) {
    if (dim.implicit_element_range) continue;
    VpiRangeDesc range;
    range.empty = VpiDimensionRangeIsEmpty(dim.kind);
    range.left_expr = dim.left_expr;
    range.right_expr = dim.right_expr;
    range.size = dim.size;
    return range;
  }
  VpiRangeDesc empty;
  empty.empty = true;
  return empty;
}

VpiHandle VpiTypespecLeftRange(const std::vector<VpiArrayDimension>& dims) {
  return VpiRangeLeftRange(LeftmostTypespecRange(dims));
}

VpiHandle VpiTypespecRightRange(const std::vector<VpiArrayDimension>& dims) {
  return VpiRangeRightRange(LeftmostTypespecRange(dims));
}

VpiHandle VpiTypespecForTypeParameter(VpiHandle type_parameter,
                                      VpiHandle resolved_typespec) {
  return resolved_typespec ? resolved_typespec : type_parameter;
}

static bool VpiTypespecUnwinds(int type) {
  switch (type) {
    case vpiArrayTypespec:
    case vpiPackedArrayTypespec:
    case vpiBitTypespec:
      return true;
    default:
      return type == vpiLogicTypespec;
  }
}

static VpiHandle VpiTypespecKey(VpiHandle typespec) {
  for (auto* child : typespec->children) {
    if (VpiIsTypespecType(child->type)) return child;
  }
  return nullptr;
}

static VpiHandle VpiVarSelectTypespec(VpiHandle select) {
  std::size_t depth = 0;
  VpiHandle array = select;
  for (; array->type == vpiVarSelect; array = array->parent) ++depth;
  VpiHandle typespec = VpiTypespecKey(array);
  for (; typespec != nullptr && depth > 0; --depth) {
    typespec = typespec->inner_typespec;
  }
  return typespec;
}

bool TryResolveTypespecRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (ref->type == vpiVarSelect && type == vpiTypespec) {
    out = VpiVarSelectTypespec(ref);
    return true;
  }
  if (ref->type == vpiTypespecMember && type == vpiExpr) {
    out = VpiTypespecMemberDefaultExpr(ref);
    return true;
  }
  if (!VpiIsTypespecType(ref->type)) return false;
  switch (type) {
    case vpiElemTypespec:
      out = VpiTypespecElemTypespec(VpiTypespecUnwinds(ref->type),
                                    ref->inner_typespec);
      return true;
    case vpiBaseTypespec:
      out = ref->type == vpiEnumTypespec ? ref->inner_typespec : nullptr;
      return true;
    case vpiIndexTypespec:
      out = VpiTypespecIndexTypespec(ref->array_type == vpiAssocArray, false,
                                     VpiTypespecKey(ref));
      return true;
    case vpiLeftRange:
      out = ref->left_range;
      return true;
    case vpiRightRange:
      out = ref->right_range;
      return true;
    default:
      return false;
  }
}

}  // namespace delta
