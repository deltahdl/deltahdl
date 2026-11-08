#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "simulator/class_object.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiDimensionRangeIsEmpty(VpiDimensionKind kind) {
  switch (kind) {
    case VpiDimensionKind::kDynamic:
    case VpiDimensionKind::kQueue:
    case VpiDimensionKind::kAssoc:
      return true;
    default:
      return false;
  }
}

int VpiRangeSize(const VpiRangeDesc& range) {
  return range.empty ? 0 : range.size;
}

VpiHandle VpiRangeLeftRange(const VpiRangeDesc& range) {
  return range.empty ? nullptr : range.left_expr;
}

VpiHandle VpiRangeRightRange(const VpiRangeDesc& range) {
  return range.empty ? nullptr : range.right_expr;
}

bool VpiIsVariablesType(int type) {
  if (VpiIsLogicVarType(type) || VpiIsArrayVarType(type)) return true;
  switch (type) {
    case vpiShortRealVar:
    case vpiRealVar:
    case vpiByteVar:
    case vpiShortIntVar:
    case vpiIntVar:
    case vpiLongIntVar:
    case vpiIntegerVar:
    case vpiTimeVar:
    case vpiPackedArrayVar:
    case vpiBitVar:
    case vpiStructVar:
    case vpiUnionVar:
    case vpiEnumVar:
    case vpiStringVar:
    case vpiChandleVar:
    case vpiClassVar:
    case vpiVirtualInterfaceVar:
    case vpiVarBit:
      return true;
    default:
      return false;
  }
}

bool VpiIsLogicVarType(int type) { return type == vpiLogicVar; }

bool VpiIsArrayVarType(int type) { return type == vpiArrayVar; }

bool VpiIsArrayVar(int unpacked_range_count) {
  return unpacked_range_count >= 1;
}

bool VpiVariableIsArrayMember(VpiHandle var) {
  return var != nullptr && var->parent != nullptr &&
         (VpiIsArrayVarType(var->parent->type) ||
          var->parent->type == vpiNamedEventArray);
}

bool VpiVariableIsStructUnionMember(VpiHandle var) {
  if (!var || var->type == vpiRegBit || !var->parent) return false;
  return var->parent->type == vpiStructVar || var->parent->type == vpiUnionVar;
}

bool VpiIsPackedArrayVarElementType(int type) {
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

bool VpiIsStructUnionOrClassVar(int type) {
  return type == vpiStructVar || type == vpiUnionVar || type == vpiClassVar;
}

bool VpiIsVariableSelectType(int type) {
  return type == vpiBitSelect || type == vpiPartSelect ||
         type == vpiIndexedPartSelect;
}

bool VpiIsVariableArrayType(int type) {
  return VpiIsArrayVarType(type) || type == vpiPackedArrayVar;
}

bool VpiIsVariableSelectOrMemberType(int type) {
  return VpiIsVariableSelectType(type) || type == vpiVarSelect ||
         VpiIsVariablesType(type);
}

static void VpiAppendVirtualInterfaceArrayElems(VpiHandle array_var,
                                                std::vector<VpiHandle>& out) {
  for (auto* elem : array_var->children) {
    if (elem->type == vpiVirtualInterfaceVar) out.push_back(elem);
  }
}

std::vector<VpiHandle> VpiScopeVirtualInterfaceVars(VpiHandle scope) {
  std::vector<VpiHandle> vifs;
  if (!scope || scope->type == vpiClassDefn) return vifs;
  for (auto* child : scope->children) {
    if (child->type == vpiVirtualInterfaceVar) {
      vifs.push_back(child);
    } else if (VpiIsVirtualInterfaceArray(child)) {
      VpiAppendVirtualInterfaceArrayElems(child, vifs);
    }
  }
  return vifs;
}

std::vector<VpiHandle> VpiScopeVariables(VpiHandle scope) {
  std::vector<VpiHandle> variables;
  if (!scope) return variables;
  for (auto* child : scope->children) {
    if (VpiIsVariablesType(child->type)) variables.push_back(child);
  }
  return variables;
}

bool VpiArrayVarIsMemory(VpiHandle var) {
  if (!var || !VpiIsArrayVarType(var->type)) return false;
  for (auto* child : var->children) {
    if (child->type == kVpiReg) return true;
  }
  return false;
}

bool VpiVariableIsPackedArrayMember(VpiHandle var) {
  if (!var || !var->parent || var->parent->type != vpiPackedArrayVar) {
    return false;
  }
  return VpiIsPackedArrayVarElementType(var->type);
}

bool VpiVarSelectConstantSelectOf(VpiHandle select) {
  if (!select || select->type != vpiVarSelect) return false;

  VpiVarSelectConstantSelectQuery query;

  query.all_indices_constant = true;
  for (const VpiObject* child : select->children) {
    if (!VpiIsExprOperandType(child->type)) continue;
    if (child->type != vpiConstant) query.all_indices_constant = false;
  }

  VpiHandle parent = select->parent;
  query.parent_is_unpacked_static_array = parent != nullptr &&
                                          parent->type == vpiArrayVar &&
                                          parent->array_type == vpiStaticArray;

  if (parent != nullptr) {
    query.parent_constant_select = parent->type == vpiVarSelect
                                       ? VpiVarSelectConstantSelectOf(parent)
                                       : !parent->automatic;
  }

  return VpiVarSelectConstantSelect(query);
}

bool VpiVarSelectConstantSelect(const VpiVarSelectConstantSelectQuery& query) {
  return query.all_indices_constant && query.parent_is_unpacked_static_array &&
         query.parent_constant_select;
}

VpiHandle VpiVariableInitExpr(VpiHandle var) {
  return var != nullptr ? var->decl_facts.init_expr : nullptr;
}

bool VpiSizeChangeCallbackApplies(int array_type, bool is_string_var) {
  if (is_string_var) return true;
  return array_type == vpiDynamicArray || array_type == vpiAssocArray ||
         array_type == vpiQueueArray;
}

std::vector<VpiRangeDesc> VpiArrayVarRanges(
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
  return VpiRangeLeftRange(LeftmostVariableRange(dims, has_members));
}

VpiHandle VpiVariableRightRange(const std::vector<VpiArrayDimension>& dims,
                                bool has_members) {
  return VpiRangeRightRange(LeftmostVariableRange(dims, has_members));
}

VpiHandle VpiSelectSingleIndex(
    const std::vector<VpiHandle>& indices_inner_to_outer) {
  if (indices_inner_to_outer.empty()) return nullptr;
  return indices_inner_to_outer.front();
}

std::vector<VpiHandle> VpiSelectIndicesOutward(
    const std::vector<VpiHandle>& indices_inner_to_outer) {
  return indices_inner_to_outer;
}

int VpiVariableSize(const VpiVariableSizeQuery& query) {
  if (VpiIsArrayVarType(query.var_type)) {
    return query.array_element_count;
  }
  if (VpiIsLogicVarType(query.var_type)) {
    return query.bit_width;
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
      return query.bit_width;
    case vpiStructVar:
    case vpiUnionVar:
      return query.packed ? query.bit_width : query.field_count;
    case vpiStringVar:
      return query.string_length;
    case vpiVarBit:
      return 1;
    case vpiVarSelect:
      return query.bit_width;
    default:
      return 0;
  }
}

int VpiFunctionSize(bool is_void_function, bool return_size_defined,
                    int return_var_size) {
  if (is_void_function) return 0;
  if (return_size_defined) return return_var_size;
  return 0;
}

bool VpiVariableHasValueProperty(int var_type, bool vpi_vector) {
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
  return value == vpiRand || value == vpiRandC || value == vpiNotRand;
}

bool VpiIsRandomized(bool active_for_randomization) {
  return active_for_randomization;
}

int VpiRandTypeOf(VpiHandle obj) {
  if (obj->rand_type != 0) return obj->rand_type;
  return VpiIsVariablesType(obj->type) ? vpiNotRand : vpiUndefined;
}

bool VpiVariableIsRandomized(VpiHandle var) {
  if (var->rand_type != vpiRand && var->rand_type != vpiRandC) return false;
  const ClassObject* holder = var->property_of;
  if (holder == nullptr) return VpiIsRandomized(true);
  const auto& states = var->automatic || holder->type == nullptr
                           ? holder->rand_active
                           : holder->type->static_rand_active;
  const auto kState = states.find(std::string(var->name));
  return VpiIsRandomized(kState == states.end() || kState->second);
}

bool VpiIsArrayTypeValue(int value) {
  return value == vpiStaticArray || value == vpiDynamicArray ||
         value == vpiAssocArray || value == vpiQueueArray;
}

bool VpiVariableScalar(const VpiScalarVectorQuery& query) {
  if (VpiIsLogicVarType(query.var_type) || query.var_type == vpiBitVar) {
    return !query.has_packed_dimension;
  }
  if (query.var_type == vpiVarBit) return true;
  if (query.var_type == vpiEnumVar) return query.base_is_scalar;
  if (VpiIsArrayVarType(query.var_type)) return query.element_is_scalar;
  return false;
}

bool VpiVariableVector(const VpiScalarVectorQuery& query) {
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
  if (!is_class_member) return vpiPublicVis;
  if (declared_visibility == vpiLocalVis ||
      declared_visibility == vpiProtectedVis) {
    return declared_visibility;
  }
  return vpiPublicVis;
}

int VpiObjectVisibility(VpiHandle obj) {
  const bool kClassMember =
      (obj->parent != nullptr && obj->parent->type == vpiClassDefn) ||
      obj->property_of != nullptr;
  if (VpiIsClassMethodType(obj->type)) {
    return VpiTaskFuncVisibility(kClassMember, obj->decl_facts.visibility);
  }
  if (VpiIsVariablesType(obj->type)) {
    return VpiVariableVisibility(kClassMember, obj->decl_facts.visibility);
  }
  return vpiUndefined;
}

bool VpiTaskFuncIsMethod(VpiHandle tf) {
  if (!tf || !VpiIsClassMethodType(tf->type)) return false;
  return tf->parent != nullptr && tf->parent->type == vpiClassDefn;
}

bool VpiFunctionIsSigned(VpiHandle function) {
  if (!function || function->type != vpiFunction) return false;
  const VpiObject* ret = function->return_var;
  if (ret == nullptr) return false;
  switch (ret->type) {
    case vpiByteVar:
    case vpiShortIntVar:
    case vpiIntVar:
    case vpiLongIntVar:
    case vpiIntegerVar:
      return true;
    default:
      return false;
  }
}

int VpiTaskFuncVisibility(bool is_class_member, int declared_visibility) {
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
  if (!is_static) return std::string();
  std::string result;
  if (!scope_path.empty()) {
    result += std::string(scope_path) + ".";
  }
  result += std::string(class_defn) + "::" + std::string(member);
  return result;
}

bool VpiIsNonStaticClassDataMember(VpiHandle obj) {
  if (!VpiIsVariablesType(obj->type)) return false;
  if (obj->property_of != nullptr) return obj->automatic;
  return obj->parent != nullptr && obj->parent->type == vpiClassDefn &&
         obj->full_name.empty();
}

VpiHandle VpiVariableParent(const std::vector<VpiParentPrefix>& prefixes) {
  for (const auto& prefix : prefixes) {
    if (prefix.qualifies) return prefix.handle;
  }
  return nullptr;
}

VpiHandle VpiLargestContainingArray(
    const std::vector<VpiHandle>& nested_innermost_first) {
  if (nested_innermost_first.empty()) return nullptr;
  return nested_innermost_first.back();
}

bool VpiConstantSelect(const VpiConstantSelectQuery& query) {
  if (query.has_static_lifetime && !query.has_parent) return true;
  return query.all_indices_constant && query.all_elements_static_members;
}

std::string VpiVariableName(const VpiVariableNameParts& parts) {
  return parts.member + parts.index_suffix;
}

std::string VpiVariableDecompile(const VpiVariableNameParts& parts) {
  std::string result;
  for (const auto& prefix : parts.member_prefixes) {
    result += prefix + ".";
  }
  result += parts.member + parts.index_suffix;
  return result;
}

std::string VpiStructMemberDecompileOf(VpiHandle var) {
  const VpiObject* named =
      var->type == vpiRegBit || var->type == vpiNetBit ? var->parent : var;
  VpiVariableNameParts parts;
  parts.member = std::string(var->name);
  for (const VpiObject* holder = named->parent;
       holder != nullptr && VpiIsStructOrUnionType(holder->type);
       holder = holder->parent) {
    parts.member_prefixes.insert(parts.member_prefixes.begin(),
                                 std::string(holder->name));
  }
  return VpiVariableDecompile(parts);
}

std::string VpiVariableFullName(const VpiVariableNameParts& parts) {
  std::string decompile = VpiVariableDecompile(parts);
  if (parts.top_scope.empty()) return decompile;
  return parts.top_scope + "." + decompile;
}

bool VpiIsStructOrUnionType(int type) {
  return type == vpiStructVar || type == vpiUnionVar || type == vpiStructNet ||
         type == vpiUnionNet;
}

std::vector<VpiHandle> VpiStructUnionMembers(VpiHandle aggregate) {
  std::vector<VpiHandle> members;
  if (!aggregate) return members;
  const bool kHoldsVariables =
      aggregate->type == vpiStructVar || aggregate->type == vpiUnionVar;
  for (auto* child : aggregate->children) {
    if (child->parent != aggregate) continue;
    const bool kIsMember =
        kHoldsVariables
            ? VpiIsVariablesType(child->type) &&
                  VpiVariableIsStructUnionMember(child)
            : VpiIsNetsType(child->type) && VpiNetStructUnionMember(child);
    if (kIsMember) members.push_back(child);
  }
  return members;
}

bool VpiIsEntireUnpackedStructOrUnion(int type, bool packed) {
  return VpiIsStructOrUnionType(type) && !packed;
}

VpiHandle VpiTypeParameterTypespec(VpiHandle type_parameter) {
  if (!type_parameter || type_parameter->type != vpiTypeParameter) {
    return nullptr;
  }
  return type_parameter->param_typespec;
}

VpiHandle VpiParameterDefaultExpr(VpiHandle parameter) {
  if (!parameter || (parameter->type != vpiParameter &&
                     parameter->type != vpiTypeParameter)) {
    return nullptr;
  }
  return parameter->param_default;
}

VpiHandle VpiParamAssignLhs(VpiHandle param_assign) {
  if (!param_assign || param_assign->type != vpiParamAssign) return nullptr;
  for (auto* child : param_assign->children) {
    if (child->type == vpiParameter || child->type == vpiTypeParameter) {
      return child;
    }
  }
  return nullptr;
}

VpiHandle VpiParameterLeftRange(VpiHandle parameter) {
  if (!parameter || parameter->type != vpiParameter ||
      !parameter->explicit_param_range) {
    return nullptr;
  }
  return parameter->param_left_range;
}

VpiHandle VpiParameterRightRange(VpiHandle parameter) {
  if (!parameter || parameter->type != vpiParameter ||
      !parameter->explicit_param_range) {
    return nullptr;
  }
  return parameter->param_right_range;
}

bool VpiIsVariableDriverType(int type) {
  switch (type) {
    case vpiPort:
    case vpiForce:
    case vpiContAssign:
    case vpiContAssignBit:
    case vpiAssignStmt:
      return true;
    default:
      return false;
  }
}

bool VpiIsVariableLoadType(int type) {
  switch (type) {
    case vpiForce:
    case vpiContAssign:
    case vpiContAssignBit:
    case vpiAssignStmt:
      return true;
    default:
      return false;
  }
}

}  // namespace delta
