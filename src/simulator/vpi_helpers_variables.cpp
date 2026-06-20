#include "simulator/vpi.h"

#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/dpi.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"

namespace delta {

bool VpiDimensionRangeIsEmpty(VpiDimensionKind kind) {
  // §37.22 detail 1: dynamic-array, queue, and associative dimensions have no
  // fixed bounds and are represented by an empty range. Fixed packed and
  // unpacked dimensions are not empty.
  switch (kind) {
    case VpiDimensionKind::kDynamic:
    case VpiDimensionKind::kQueue:
    case VpiDimensionKind::kAssoc:
      return true;
    case VpiDimensionKind::kPacked:
    case VpiDimensionKind::kFixedUnpacked:
      return false;
  }
  return false;
}

int VpiRangeSize(const VpiRangeDesc& range) {
  // §37.22 detail 2: an empty range reports a size of 0.
  return range.empty ? 0 : range.size;
}

VpiHandle VpiRangeLeftRange(const VpiRangeDesc& range) {
  // §37.22 detail 2: an empty range returns NULL for vpiLeftRange.
  return range.empty ? nullptr : range.left_expr;
}

VpiHandle VpiRangeRightRange(const VpiRangeDesc& range) {
  // §37.22 detail 2: an empty range returns NULL for vpiRightRange.
  return range.empty ? nullptr : range.right_expr;
}

// ===========================================================================
// §37.17 Variables.
// ===========================================================================

bool VpiIsLogicVarType(int type) {
  // §37.17 detail 19: a logic var and a reg are the same object kind.
  return type == vpiLogicVar || type == kVpiReg;
}

bool VpiIsArrayVarType(int type) {
  // §37.17 detail 19: an array var and a reg array are the same object kind.
  return type == vpiArrayVar || type == vpiRegArray;
}

bool VpiIsArrayVar(int unpacked_range_count) {
  // §37.17 detail 1: one or more unpacked ranges makes a variable an array var.
  return unpacked_range_count >= 1;
}

bool VpiVariableIsArrayMember(VpiHandle var) {
  // §37.17 detail 2: a variable is an array member when its vpiParent prefix is
  // an array variable.
  return var != nullptr && var->parent != nullptr &&
         VpiIsArrayVarType(var->parent->type);
}

bool VpiVariableIsStructUnionMember(VpiHandle var) {
  // §37.17 detail 17: a variable is a struct/union member when its vpiParent
  // prefix is a struct or union variable.
  if (!var || !var->parent) return false;
  return var->parent->type == vpiStructVar || var->parent->type == vpiUnionVar;
}

bool VpiIsPackedArrayVarElementType(int type) {
  // §37.18 detail 3: a packed array variable's subelements are packed struct
  // var, union var, or enum var objects; for a multidimensioned packed array a
  // subelement is itself another packed array var (the leftmost packed range
  // removed). vpiElement walks exactly these kinds.
  switch (type) {
    case vpiStructVar:
    case vpiUnionVar:
    case vpiEnumVar:
    case vpiPackedArrayVar:
      return true;
    default:
      return false;
  }
}

bool VpiVariableIsPackedArrayMember(VpiHandle var) {
  // §37.18 detail 4: vpiPackedArrayMember is TRUE for a struct var, union var,
  // enum var, or packed array var whose vpiParent prefix is a packed array var.
  // The vpiParent prefix is resolved by §37.17 detail 26; here the property is
  // simply that prefix being a packed array var with the element being one of
  // those four kinds.
  if (!var || !var->parent || var->parent->type != vpiPackedArrayVar) {
    return false;
  }
  return VpiIsPackedArrayVarElementType(var->type);
}

bool VpiVarSelectConstantSelect(const VpiVarSelectConstantSelectQuery& query) {
  // §37.19 detail 1: a var select is a constant select only when all three
  // conditions hold together - every index is an elaboration-time constant, the
  // parent is an unpacked array with static bounds, and the parent is itself a
  // constant select. If any condition fails the property is FALSE.
  return query.all_indices_constant && query.parent_is_unpacked_static_array &&
         query.parent_constant_select;
}

VpiHandle VpiVariableInitExpr(VpiHandle var) {
  // §37.17 detail 8: when a variable has an initialization expression, it is
  // reached through vpiExpr - modeled as the variable's first child. A variable
  // with no initialization expression has none.
  if (!var || var->children.empty()) return nullptr;
  return var->children.front();
}

bool VpiSizeChangeCallbackApplies(int array_type, bool is_string_var) {
  // §37.17 detail 14: cbSizeChange applies only to dynamic arrays, associative
  // arrays, queues, and string variables; not to fixed-size (static) arrays or
  // any other variable.
  if (is_string_var) return true;
  return array_type == vpiDynamicArray || array_type == vpiAssocArray ||
         array_type == vpiQueueArray;
}

std::vector<VpiRangeDesc> VpiArrayVarRanges(
    const std::vector<VpiArrayDimension>& dims) {
  // §37.17 detail 4: one range per dimension, leftmost to rightmost. Each
  // dimension routes through §37.22: a dynamic/queue/associative dimension is
  // an empty range, a fixed dimension keeps its bounds. The implicit range of a
  // packed struct/union element or an enum var's base type is excluded.
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

// §37.17 detail 6: build the §37.22 range for a variable's leftmost dimension,
// the one vpiLeftRange/vpiRightRange report. Returns an empty range (so both
// relations yield NULL) when the variable has no members or no dimensions.
static VpiRangeDesc LeftmostVariableRange(
    const std::vector<VpiArrayDimension>& dims, bool has_members) {
  if (!has_members || dims.empty()) {
    VpiRangeDesc empty;
    empty.empty = true;
    return empty;
  }
  const VpiArrayDimension& dim = dims.front();
  VpiRangeDesc range;
  range.empty = VpiDimensionRangeIsEmpty(dim.kind);
  range.left_expr = dim.left_expr;
  range.right_expr = dim.right_expr;
  range.size = dim.size;
  return range;
}

VpiHandle VpiVariableLeftRange(const std::vector<VpiArrayDimension>& dims,
                               bool has_members) {
  // §37.17 detail 6: defer to §37.22's vpiLeftRange, which returns NULL for an
  // empty leftmost range.
  return VpiRangeLeftRange(LeftmostVariableRange(dims, has_members));
}

VpiHandle VpiVariableRightRange(const std::vector<VpiArrayDimension>& dims,
                                bool has_members) {
  // §37.17 detail 6: the mirror of VpiVariableLeftRange.
  return VpiRangeRightRange(LeftmostVariableRange(dims, has_members));
}

VpiHandle VpiSelectSingleIndex(
    const std::vector<VpiHandle>& indices_inner_to_outer) {
  // §37.17 detail 5: the index of a var select in a one-dimensional array is
  // its single innermost index.
  if (indices_inner_to_outer.empty()) return nullptr;
  return indices_inner_to_outer.front();
}

std::vector<VpiHandle> VpiSelectIndicesOutward(
    const std::vector<VpiHandle>& indices_inner_to_outer) {
  // §37.17 details 5, 13, and 18: the iteration runs from the innermost index
  // outward, which is the order the inputs are already in.
  return indices_inner_to_outer;
}

int VpiVariableSize(const VpiVariableSizeQuery& query) {
  // §37.17 details 9 and 10: vpiSize depends on the kind of variable.
  if (VpiIsArrayVarType(query.var_type)) {
    return query.array_element_count;  // variable array -> element count
  }
  if (VpiIsLogicVarType(query.var_type)) {
    return query.bit_width;  // logic var (reg) -> size in bits
  }
  switch (query.var_type) {
    case vpiByteVar:
    case vpiShortIntVar:
    case vpiIntVar:
    case vpiLongIntVar:
    case vpiIntegerVar:
    case vpiTimeVar:
    case vpiBitVar:
    case vpiEnumVar:
    case vpiPackedArrayVar:
      return query.bit_width;  // integer-typed/packed/enum -> size in bits
    case vpiStructVar:
    case vpiUnionVar:
      // packed -> size in bits; unpacked -> number of fields
      return query.packed ? query.bit_width : query.field_count;
    case vpiStringVar:
      return query.string_length;  // current character count
    case vpiVarBit:
      return 1;  // a var bit is one bit
    case vpiVarSelect:
      return query.bit_width;  // bits in the (packed) var select
    default:
      return 0;  // behavior of vpiSize not defined for other variables
  }
}

int VpiFunctionSize(bool is_void_function, bool return_size_defined,
                    int return_var_size) {
  // §37.41 detail 12: a void function has no return value, so its size is 0.
  // Otherwise, when the vpiReturn variable's size is defined and determinable
  // without evaluating the function, the function's size is that variable's
  // size (§37.17 detail 9 is what defines the variable's size). Every remaining
  // case is undefined; report 0, the same not-defined value VpiVariableSize
  // uses.
  if (is_void_function) return 0;
  if (return_size_defined) return return_var_size;
  return 0;
}

bool VpiVariableHasValueProperty(int var_type, bool vpi_vector) {
  // §37.17 detail 11: array, class, and virtual-interface variables have no
  // value property, and neither does an unpacked struct/union (vpiVector
  // FALSE).
  if (VpiIsArrayVarType(var_type) || var_type == vpiClassVar ||
      var_type == vpiVirtualInterfaceVar) {
    return false;
  }
  if ((var_type == vpiStructVar || var_type == vpiUnionVar) && !vpi_vector) {
    return false;
  }
  return true;
}

bool VpiBitIteratorApplies(int var_type, bool packed) {
  // §37.17 detail 12: vpiBit applies to logic, bit, packed struct, packed
  // union, and packed array variables only.
  if (VpiIsLogicVarType(var_type) || var_type == vpiBitVar ||
      var_type == vpiPackedArrayVar) {
    return true;
  }
  if (var_type == vpiStructVar || var_type == vpiUnionVar) {
    return packed;
  }
  return false;
}

bool VpiIsRandTypeValue(int value) {
  // §37.17 details 15 and 22: the three randomization types.
  return value == vpiRand || value == vpiRandC || value == vpiNotRand;
}

bool VpiIsRandomized(bool active_for_randomization) {
  // §37.17 detail 16: vpiIsRandomized is exactly that activeness.
  return active_for_randomization;
}

bool VpiIsArrayTypeValue(int value) {
  // §37.17 detail 21: the four array-type values.
  return value == vpiStaticArray || value == vpiDynamicArray ||
         value == vpiAssocArray || value == vpiQueueArray;
}

bool VpiVariableScalar(const VpiScalarVectorQuery& query) {
  // §37.17 detail 20: a bit/logic var with no packed dimension and a var bit
  // are scalars; an enum var defers to its base typespec; an array var defers
  // to an element; every other variable kind is not a scalar.
  if (VpiIsLogicVarType(query.var_type) || query.var_type == vpiBitVar) {
    return !query.has_packed_dimension;
  }
  if (query.var_type == vpiVarBit) return true;
  if (query.var_type == vpiEnumVar) return query.base_is_scalar;
  if (VpiIsArrayVarType(query.var_type)) return query.element_is_scalar;
  return false;
}

bool VpiVariableVector(const VpiScalarVectorQuery& query) {
  // §37.17 detail 20: a packed bit/logic var, a packed struct/union/array var,
  // and the integer-typed vars are vectors; an enum var defers to its base
  // typespec; an array var defers to an element; everything else is not a
  // vector.
  if (VpiIsLogicVarType(query.var_type) || query.var_type == vpiBitVar) {
    return query.has_packed_dimension;
  }
  if (query.var_type == vpiPackedArrayVar) return true;
  if (query.var_type == vpiStructVar || query.var_type == vpiUnionVar) {
    return query.packed;
  }
  if (query.var_type == vpiVarBit) return false;
  if (query.var_type == vpiEnumVar) return query.base_is_vector;
  switch (query.var_type) {
    case vpiIntegerVar:
    case vpiTimeVar:
    case vpiShortIntVar:
    case vpiIntVar:
    case vpiLongIntVar:
    case vpiByteVar:
      return true;
    default:
      break;
  }
  if (VpiIsArrayVarType(query.var_type)) return query.element_is_vector;
  return false;
}

int VpiVariableVisibility(bool is_class_member, int declared_visibility) {
  // §37.17 detail 24: a non-class-member variable, and a class member that is
  // neither local nor protected, reports vpiPublicVis.
  if (!is_class_member) return vpiPublicVis;
  if (declared_visibility == vpiLocalVis ||
      declared_visibility == vpiProtectedVis) {
    return declared_visibility;
  }
  return vpiPublicVis;
}

int VpiTaskFuncVisibility(bool is_class_member, int declared_visibility) {
  // §37.41 detail 4: a task or function that is not a class member, and a class
  // member (method) that is neither local nor protected, reports vpiPublicVis;
  // a local or protected method reports its declared visibility.
  if (!is_class_member) return vpiPublicVis;
  if (declared_visibility == vpiLocalVis ||
      declared_visibility == vpiProtectedVis) {
    return declared_visibility;
  }
  return vpiPublicVis;
}

std::string VpiClassMemberFullName(bool is_static, std::string_view scope_path,
                                   std::string_view class_defn,
                                   std::string_view member) {
  // §37.17 detail 25: a non-static class data member has no full name; a static
  // member's full name routes through the "class defn" with "::", e.g.
  // "top.Packet::Id".
  if (!is_static) return std::string();
  std::string result;
  if (!scope_path.empty()) {
    result += std::string(scope_path) + ".";
  }
  result += std::string(class_defn) + "::" + std::string(member);
  return result;
}

VpiHandle VpiVariableParent(const std::vector<VpiParentPrefix>& prefixes) {
  // §37.17 detail 26: scan the prefixes rightmost to leftmost and return the
  // first one that qualifies; NULL when none does.
  for (const auto& prefix : prefixes) {
    if (prefix.qualifies) return prefix.handle;
  }
  return nullptr;
}

VpiHandle VpiLargestContainingArray(
    const std::vector<VpiHandle>& nested_innermost_first) {
  // §37.17 detail 26: the largest containing array is the outermost of the
  // nested array prefixes (the last entry when given innermost first).
  if (nested_innermost_first.empty()) return nullptr;
  return nested_innermost_first.back();
}

bool VpiConstantSelect(const VpiConstantSelectQuery& query) {
  // §37.17 detail 27: a static-lifetime variable with no parent is a constant
  // select, as is a select whose indices are all elaboration-time constants and
  // whose elements are all struct/union members or static-bound array elements.
  if (query.has_static_lifetime && !query.has_parent) return true;
  return query.all_indices_constant && query.all_elements_static_members;
}

std::string VpiVariableName(const VpiVariableNameParts& parts) {
  // §37.17 detail 28: the leaf member and its own index/slice, no prefixes.
  return parts.member + parts.index_suffix;
}

std::string VpiVariableDecompile(const VpiVariableNameParts& parts) {
  // §37.17 detail 28: the struct/union/class-var prefixes joined to the member,
  // without the top-level scope.
  std::string result;
  for (const auto& prefix : parts.member_prefixes) {
    result += prefix + ".";
  }
  result += parts.member + parts.index_suffix;
  return result;
}

std::string VpiVariableFullName(const VpiVariableNameParts& parts) {
  // §37.17 detail 28: the top-level scope prefixed to the decompile form.
  std::string decompile = VpiVariableDecompile(parts);
  if (parts.top_scope.empty()) return decompile;
  return parts.top_scope + "." + decompile;
}

// ===========================================================================
// §37.25 Typespec (the typespec object model; range relations route through
// §37.22, and a member's expr role reuses §37.59's expr class).
// ===========================================================================

bool VpiIsTypespecType(int type) {
  // §37.25: every "... typespec" node of Figure 37.25 - the built-in scalar and
  // integer typespecs, the user-defined-type typespecs, the array/packed-array
  // typespecs, and (detail 11) an unresolved type parameter, which acts as a
  // typespec. Each numeric value is listed once; some Annex M spellings (e.g.
  // vpiChandleTypespec, vpiIntegerTypespec, vpiTimeTypespec, vpiRealTypespec)
  // share a value with a name already covered here.
  switch (type) {
    case vpiTypespec:
    case vpiTypeParameter:
    case vpiLongIntTypespec:
    case vpiShortIntTypespec:
    case vpiIntTypespec:
    case vpiShortRealTypespec:
    case vpiByteTypespec:
    case vpiClassTypespec:
    case vpiStringTypespec:
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

VpiHandle VpiTypespecMemberTypespec(VpiHandle member) {
  // §37.25 detail 3: the member's type is its typespec child.
  if (!member) return nullptr;
  for (auto* child : member->children) {
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

// ===========================================================================
// §37.26 Structures and unions.
// ===========================================================================

bool VpiIsStructOrUnionType(int type) {
  // §37.26 (figure): the structure/union object kinds - a struct or union
  // declared as a variable, and a struct or union declared as a net.
  return type == vpiStructVar || type == vpiUnionVar || type == vpiStructNet ||
         type == vpiUnionNet;
}

bool VpiIsEntireUnpackedStructOrUnion(int type, bool packed) {
  // §37.26 detail 1: the value-access restriction applies to an entire unpacked
  // structure or union. A packed aggregate has a single vector value and is
  // accessible, so the restriction is the struct/union kinds with vpiPacked
  // false.
  return VpiIsStructOrUnionType(type) && !packed;
}

// ===========================================================================
// §37.28 Parameter, spec param, def param, param assign.
// ===========================================================================

VpiHandle VpiTypeParameterTypespec(VpiHandle type_parameter) {
  // §37.28 detail 2: hand back the stored typespec verbatim. The detail asks
  // for the typespec the type parameter has at the end of elaboration "without
  // resolving typedef aliases", so we deliberately do not run §37.25/§37.30's
  // alias resolution here - the recorded typespec is returned as-is, even when
  // it is itself a typedef alias.
  if (!type_parameter || type_parameter->type != vpiTypeParameter) {
    return nullptr;
  }
  return type_parameter->param_typespec;
}

VpiHandle VpiParameterDefaultExpr(VpiHandle parameter) {
  // §37.28 detail 3: vpiExpr reaches the parameter's default - a value
  // parameter's default value expression, or a type parameter's default
  // typespec. Both are kept in the same designated slot.
  if (!parameter || (parameter->type != vpiParameter &&
                     parameter->type != vpiTypeParameter)) {
    return nullptr;
  }
  return parameter->param_default;
}

VpiHandle VpiParamAssignLhs(VpiHandle param_assign) {
  // §37.28 detail 4: vpiLhs reaches the overridden parameter - the value
  // parameter (vpiParameter) or type parameter (vpiTypeParameter) among the
  // param assign's children. The override target is a parameter-kind object,
  // not a child whose own type is literally vpiLhs, so the generic walk cannot
  // find it.
  if (!param_assign || param_assign->type != vpiParamAssign) return nullptr;
  for (auto* child : param_assign->children) {
    if (child->type == vpiParameter || child->type == vpiTypeParameter) {
      return child;
    }
  }
  return nullptr;
}

VpiHandle VpiParameterLeftRange(VpiHandle parameter) {
  // §37.28 detail 5: a value parameter declared without an explicit range
  // reports a null handle for vpiLeftRange; only an explicitly ranged parameter
  // reaches its left range-bound expression.
  if (!parameter || parameter->type != vpiParameter ||
      !parameter->explicit_param_range) {
    return nullptr;
  }
  return parameter->param_left_range;
}

VpiHandle VpiParameterRightRange(VpiHandle parameter) {
  // §37.28 detail 5: the mirror of VpiParameterLeftRange for vpiRightRange.
  if (!parameter || parameter->type != vpiParameter ||
      !parameter->explicit_param_range) {
    return nullptr;
  }
  return parameter->param_right_range;
}

// ===========================================================================
// §37.29 Virtual interface.
// ===========================================================================

}  // namespace delta
