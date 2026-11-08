#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/vpi_object.h"

namespace delta {

VpiHandle VpiFrameParent(VpiHandle frame);

VpiHandle VpiFrameOrigin(VpiHandle frame);

VpiHandle VpiFrameStmt(VpiHandle frame);

VpiHandle VpiFrameThread(VpiHandle frame);

std::vector<VpiHandle> VpiFrameAutomatics(VpiHandle frame);

VpiHandle VpiThreadParent(VpiHandle thread);

VpiHandle VpiThreadOrigin(VpiHandle thread);

VpiHandle VpiThreadFrame(VpiHandle thread);

bool VpiTryResolveThreadRelation(int type, VpiHandle ref, VpiHandle& out);

bool VpiTryResolveFrameRelation(int type, VpiHandle ref, VpiHandle& out);

bool VpiCollectFrameAutomatics(int type, VpiHandle ref, VpiHandle iter);

std::vector<VpiHandle> VpiThreadThreads(VpiHandle thread);

struct VpiRangeDesc {
  bool empty = false;
  VpiHandle left_expr = nullptr;
  VpiHandle right_expr = nullptr;
  int size = 0;
};

enum class VpiDimensionKind : std::uint8_t {
  kPacked,
  kFixedUnpacked,
  kDynamic,
  kQueue,
  kAssoc,
};

bool VpiDimensionRangeIsEmpty(VpiDimensionKind kind);

int VpiRangeSize(const VpiRangeDesc& range);

VpiHandle VpiRangeLeftRange(const VpiRangeDesc& range);

VpiHandle VpiRangeRightRange(const VpiRangeDesc& range);

bool VpiIsVariablesType(int type);

bool VpiIsExprOperandType(int type);

bool VpiIsOperandObject(VpiHandle obj);

std::optional<int64_t> VpiElaborationValue(const VpiObject* expr);

bool VpiIsElaborationConstant(const VpiObject* expr);

bool TryResolveSelectRelation(int type, VpiHandle ref, VpiHandle& out);

bool VpiIsStructUnionOrClassVar(int type);

bool VpiIsVariableSelectType(int type);

bool VpiIsVariableArrayType(int type);

bool VpiIsVariableSelectOrMemberType(int type);

std::vector<VpiHandle> VpiScopeVirtualInterfaceVars(VpiHandle scope);

std::vector<VpiHandle> VpiScopeVariables(VpiHandle scope);

bool VpiArrayVarIsMemory(VpiHandle var);

std::vector<VpiHandle> VpiStructUnionMembers(VpiHandle aggregate);

bool VpiIsLogicVarType(int type);

bool VpiIsArrayVarType(int type);

bool VpiIsArrayVar(int unpacked_range_count);

bool VpiVariableIsArrayMember(VpiHandle var);

bool VpiVariableIsStructUnionMember(VpiHandle var);

VpiHandle VpiVariableInitExpr(VpiHandle var);

bool VpiSizeChangeCallbackApplies(int array_type, bool is_string_var);

struct VpiArrayDimension {
  VpiDimensionKind kind = VpiDimensionKind::kFixedUnpacked;
  VpiHandle left_expr = nullptr;
  VpiHandle right_expr = nullptr;
  int size = 0;
  bool implicit_element_range = false;
};

std::vector<VpiRangeDesc> VpiArrayVarRanges(
    const std::vector<VpiArrayDimension>& dims);

VpiHandle VpiVariableLeftRange(const std::vector<VpiArrayDimension>& dims,
                               bool has_members);

VpiHandle VpiVariableRightRange(const std::vector<VpiArrayDimension>& dims,
                                bool has_members);

VpiHandle VpiSelectSingleIndex(
    const std::vector<VpiHandle>& indices_inner_to_outer);

std::vector<VpiHandle> VpiSelectIndicesOutward(
    const std::vector<VpiHandle>& indices_inner_to_outer);

struct VpiVariableSizeQuery {
  int var_type = 0;
  bool packed = false;
  int bit_width = 0;
  int array_element_count = 0;
  int string_length = 0;
  int field_count = 0;
};

int VpiVariableSize(const VpiVariableSizeQuery& query);

int VpiFunctionSize(bool is_void_function, bool return_size_defined,
                    int return_var_size);

bool VpiVariableHasValueProperty(int var_type, bool vpi_vector);

bool VpiBitIteratorApplies(int var_type, bool packed);

bool VpiIsRandTypeValue(int value);

bool VpiIsRandomized(bool active_for_randomization);

int VpiRandTypeOf(VpiHandle obj);

bool VpiVariableIsRandomized(VpiHandle var);

bool VpiIsArrayTypeValue(int value);

struct VpiScalarVectorQuery {
  int var_type = 0;
  bool has_packed_dimension = false;
  bool packed = false;
  bool base_is_scalar = false;
  bool base_is_vector = false;
  bool element_is_scalar = false;
  bool element_is_vector = false;
};

bool VpiVariableScalar(const VpiScalarVectorQuery& query);

bool VpiVariableVector(const VpiScalarVectorQuery& query);

int VpiVariableVisibility(bool is_class_member, int declared_visibility);

int VpiTaskFuncVisibility(bool is_class_member, int declared_visibility);

int VpiObjectVisibility(VpiHandle obj);

bool VpiTaskFuncIsMethod(VpiHandle tf);

bool VpiFunctionIsSigned(VpiHandle function);

std::string VpiClassMemberFullName(bool is_static, std::string_view scope_path,
                                   std::string_view class_defn,
                                   std::string_view member);

bool VpiIsNonStaticClassDataMember(VpiHandle obj);

struct VpiParentPrefix {
  bool qualifies = false;
  VpiHandle handle = nullptr;
};

VpiHandle VpiVariableParent(const std::vector<VpiParentPrefix>& prefixes);

VpiHandle VpiLargestContainingArray(
    const std::vector<VpiHandle>& nested_innermost_first);

struct VpiConstantSelectQuery {
  bool has_static_lifetime = false;
  bool has_parent = false;
  bool all_indices_constant = false;
  bool all_elements_static_members = false;
};

bool VpiConstantSelect(const VpiConstantSelectQuery& query);

struct VpiVariableNameParts {
  std::string top_scope;
  std::vector<std::string> member_prefixes;
  std::string member;
  std::string index_suffix;
};

std::string VpiVariableName(const VpiVariableNameParts& parts);

std::string VpiStructMemberDecompileOf(VpiHandle var);

std::string VpiVariableDecompile(const VpiVariableNameParts& parts);

std::string VpiVariableFullName(const VpiVariableNameParts& parts);

bool VpiIsPackedArrayVarElementType(int type);

bool VpiVariableIsPackedArrayMember(VpiHandle var);

struct VpiVarSelectConstantSelectQuery {
  bool all_indices_constant = false;
  bool parent_is_unpacked_static_array = false;
  bool parent_constant_select = false;
};

bool VpiVarSelectConstantSelect(const VpiVarSelectConstantSelectQuery& query);

bool VpiVarSelectConstantSelectOf(VpiHandle select);

bool VpiIsTypespecType(int type);

const char* VpiTypespecName(int ts_type, bool denotes_user_typedef,
                            const char* typedef_name, const char* class_name);

VpiHandle VpiTypespecTypedefAlias(bool is_alias, VpiHandle aliased_typedef);

VpiHandle VpiTypespecIndexTypespec(bool is_assoc_array_typespec,
                                   bool wildcard_index, VpiHandle key_typespec);

std::vector<VpiHandle> VpiTypespecMembers(
    int ts_type, const std::vector<VpiHandle>& members);

VpiHandle VpiTypespecChild(VpiHandle obj);

const char* VpiTypespecMemberName(VpiHandle member);

VpiHandle VpiTypespecMemberDefaultExpr(VpiHandle member);

VpiHandle VpiTypespecElemTypespec(bool has_ranges, VpiHandle element_typespec);

std::vector<VpiRangeDesc> VpiTypespecRanges(
    const std::vector<VpiArrayDimension>& dims);

VpiHandle VpiTypespecLeftRange(const std::vector<VpiArrayDimension>& dims);

VpiHandle VpiTypespecRightRange(const std::vector<VpiArrayDimension>& dims);

VpiHandle VpiTypespecForTypeParameter(VpiHandle type_parameter,
                                      VpiHandle resolved_typespec);

bool TryResolveTypespecRelation(int type, VpiHandle ref, VpiHandle& out);

bool VpiIsVariableDriverType(int type);

bool VpiIsVariableLoadType(int type);

bool VpiAssignTargetWrites(const VpiObject* lhs, const VpiObject& target);

bool VpiExpressionReads(const VpiObject* rhs, const VpiObject& target);

const std::vector<VpiObject*>& VpiSubexpressions(const VpiObject& expr);

bool VpiIsVariableDriverOrLoad(const VpiObject& child, const VpiObject& var,
                               bool want_driver);

void VpiCollectVariableDriversOrLoads(VpiObject* node, bool want_driver,
                                      bool descend, VpiObject* iter);

void VpiHangOnVariablesNamed(VpiHandle holder, VpiHandle expr);

bool VpiIsPortsType(int type);

bool VpiIsNetDriverType(int type);

bool VpiIsNetLoadType(int type);

bool VpiPortIsComplexExpressionLoad(VpiHandle port);

bool VpiIsNetDriverOrLoad(VpiHandle child, VpiHandle net, bool want_driver);

std::vector<VpiHandle> VpiNetPortDrivers(VpiHandle net);

std::vector<VpiHandle> VpiNetsJoinedThroughPorts(VpiHandle net);

std::vector<VpiHandle> VpiNetDriversOrLoads(VpiHandle node, bool want_driver,
                                            bool local);

std::vector<VpiHandle> VpiNetLocalPorts(VpiHandle net, bool want_driver);

void VpiHangOnNetsNamed(VpiHandle holder, VpiHandle expr);

bool VpiIsStructOrUnionType(int type);

bool VpiIsEntireUnpackedStructOrUnion(int type, bool packed);

}  // namespace delta
