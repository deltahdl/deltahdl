#include <cstddef>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

// ===========================================================================
// §37.25 Typespec (the typespec object model; range relations route through
// §37.22, and a member's expr role reuses §37.59's expr class).
// ===========================================================================

bool VpiIsTypespecType(int type) {
  // §37.25: every "... typespec" node of Figure 37.25 - the built-in scalar and
  // integer typespecs, the user-defined-type typespecs, the array/packed-array
  // typespecs, and (detail 11) an unresolved type parameter, which acts as a
  // typespec.
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
  // §37.25 detail 1: a class typespec reports the class name; otherwise a
  // user-defined typedef reports the typedef's name (possibly empty for an
  // inline field, detail 5); a built-in type reports NULL.
  if (ts_type == vpiClassTypespec) return class_name;
  if (denotes_user_typedef) return typedef_name;
  return nullptr;
}

VpiHandle VpiTypespecTypedefAlias(bool is_alias, VpiHandle aliased_typedef) {
  // §37.25 detail 1: only a typespec whose typedef aliases another typedef
  // hands back the aliased typedef; otherwise vpiTypedefAlias is NULL.
  return is_alias ? aliased_typedef : nullptr;
}

VpiHandle VpiTypespecIndexTypespec(bool is_assoc_array_typespec,
                                   bool wildcard_index,
                                   VpiHandle key_typespec) {
  // §37.25 detail 2: the index typespec exists only for an associative array,
  // and a wildcard index type has none.
  if (!is_assoc_array_typespec || wildcard_index) return nullptr;
  return key_typespec;
}

std::vector<VpiHandle> VpiTypespecMembers(
    int ts_type, const std::vector<VpiHandle>& members) {
  // §37.25 detail 3: only a struct or union typespec exposes typespec members.
  if (ts_type == vpiStructTypespec || ts_type == vpiUnionTypespec) {
    return members;
  }
  return {};
}

VpiHandle VpiTypespecChild(VpiHandle obj) {
  // §37.25 detail 3: a member's type is its typespec child, as a net's or an
  // interconnect net's is (§37.24 detail 1).
  if (!obj) return nullptr;
  for (auto* child : obj->children) {
    if (VpiIsTypespecType(child->type)) return child;
  }
  return nullptr;
}

const char* VpiTypespecMemberName(VpiHandle member) {
  // §37.25 detail 4: a typespec member reports its own name.
  if (!member) return nullptr;
  return member->name.data();
}

VpiHandle VpiTypespecMemberDefaultExpr(VpiHandle member) {
  // §37.25 detail 7: a member's default value is reached as its expr child (an
  // object of the §37.59 expr class); a member without a default has none.
  if (!member) return nullptr;
  for (auto* child : member->children) {
    if (VpiIsExprType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiTypespecElemTypespec(bool has_ranges, VpiHandle element_typespec) {
  // §37.25 detail 8: unwinding the leftmost range yields the element typespec;
  // once no ranges remain there is nothing left to unwind, so it is NULL.
  return has_ranges ? element_typespec : nullptr;
}

std::vector<VpiRangeDesc> VpiTypespecRanges(
    const std::vector<VpiArrayDimension>& dims) {
  // §37.25 detail 10: one range per dimension, leftmost to rightmost, each
  // routed through §37.22 so a dynamic/queue/associative dimension becomes an
  // empty range. An implicit element range is not a declared dimension of the
  // typespec.
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

// §37.25 detail 9: the typespec's leftmost declared dimension drives
// vpiLeftRange/vpiRightRange. With no declared dimension the range is empty, so
// both relations yield NULL.
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
  // §37.25 detail 9: defer to §37.22, which yields NULL for an empty leftmost
  // range.
  return VpiRangeLeftRange(LeftmostTypespecRange(dims));
}

VpiHandle VpiTypespecRightRange(const std::vector<VpiArrayDimension>& dims) {
  // §37.25 detail 9: the mirror of VpiTypespecLeftRange.
  return VpiRangeRightRange(LeftmostTypespecRange(dims));
}

VpiHandle VpiTypespecForTypeParameter(VpiHandle type_parameter,
                                      VpiHandle resolved_typespec) {
  // §37.25 detail 11: an unresolved type parameter acts as the typespec itself.
  return resolved_typespec ? resolved_typespec : type_parameter;
}

// §37.25 detail 8: whether a typespec of the kind `type` unwinds a range at a
// time through vpiElemTypespec.
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

// §37.25 detail 2: the typespec an associative array typespec's key is, the
// one typespec among its objects.
static VpiHandle VpiTypespecKey(VpiHandle typespec) {
  for (auto* child : typespec->children) {
    if (VpiIsTypespecType(child->type)) return child;
  }
  return nullptr;
}

// §37.19 (figure): the typespec of the element a var select selects: its
// array var's typespec unwound through vpiElemTypespec once per select from
// the array down to it (§37.25 detail 8); null where the array reaches none.
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
