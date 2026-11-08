#pragma once

#include <cstdint>
#include <deque>
#include <functional>
#include <span>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

class Arena;
struct RtlirDesign;
struct UdpDecl;
struct UdpTableRow;

VpiHandle VpiTypeParameterTypespec(VpiHandle type_parameter);

VpiHandle VpiParameterDefaultExpr(VpiHandle parameter);

VpiHandle VpiParamAssignLhs(VpiHandle param_assign);

VpiHandle VpiParameterLeftRange(VpiHandle parameter);
VpiHandle VpiParameterRightRange(VpiHandle parameter);

bool VpiIsInterfaceExprType(int type);

bool VpiInterfaceExprIsValid(VpiHandle expr);

VpiHandle VpiVirtualInterfaceExpr(VpiHandle var);

const char* VpiInterfaceTypespecDefName(VpiHandle interface_typespec);

VpiHandle VpiInterfaceTypespecParent(VpiHandle interface_typespec);

VpiHandle VpiClockingBlockPrefix(VpiHandle block);

VpiHandle VpiClockingBlockActual(VpiHandle block);

bool VpiIsClockingIODeclExprType(int type);

VpiHandle VpiClockingIODeclExpr(VpiHandle io_decl);

VpiHandle VpiClockingBlockClockingEvent(VpiHandle block);

bool VpiIsIoDeclExprType(int type);

int VpiIoDeclExprType(bool passed_by_reference, bool is_interface_or_modport,
                      bool is_virtual_interface, int default_expr_type);

int VpiIoDeclDirection(int declared_direction, bool passed_by_reference,
                       bool expr_is_ref_obj_to_interface_or_modport,
                       bool expr_is_virtual_interface_var);

VpiHandle VpiIoDeclExpr(VpiHandle io_decl);

std::vector<VpiRangeDesc> VpiIoDeclRanges(
    const std::vector<VpiArrayDimension>& dims);

VpiHandle VpiIoDeclLeftRange(const std::vector<VpiArrayDimension>& dims);

VpiHandle VpiIoDeclRightRange(const std::vector<VpiArrayDimension>& dims);

bool VpiIsValidPortType(int port_type);

int VpiPortTypeFromFormal(bool formal_is_interface, bool formal_is_modport);

bool VpiPortDelaysApplicable(int port_type);

VpiHandle VpiHighConn(VpiHandle obj);

VpiHandle VpiLowConn(VpiHandle obj);

bool VpiPortLowConnSatisfiesInterfaceRule(VpiHandle port);

bool VpiPortScalar(int port_width);

bool VpiPortVector(int port_width);

inline bool VpiScalarVectorAppliesTo(int type) {
  return type == kVpiPort || type == vpiIODecl;
}

bool VpiPortIndexAndNameApply(int type);

const char* VpiPortName(bool explicitly_named, std::string_view explicit_name,
                        std::string_view inferred_name);

int VpiPortSize(bool is_null_port, int port_width);

int VpiRefObjGeneric(bool refers_to_interface, bool is_generic_interface);

const char* VpiRefObjDefName(VpiHandle ref_obj);

VpiHandle VpiRefObjTypespec(VpiHandle ref_obj);

VpiHandle VpiRefObjParent(VpiHandle ref_obj);

bool VpiIsRefObjPortRelation(int type);
std::vector<VpiHandle> VpiRefObjPorts(int type, VpiHandle ref_obj);

bool VpiIsArrayNet(int unpacked_range_count);

bool VpiIsPackedArrayNet(int net_type, int explicit_packed_range_count);

bool VpiNetIsArrayMember(VpiHandle net);

bool VpiNetIsPackedArrayMember(VpiHandle net);

bool VpiNetBitIteratorApplies(int net_type);

bool VpiNetTerminalAccessAllowed(bool is_scalar_net_or_bit_select);

enum class VpiPortGranularity : std::uint8_t {
  kPortBits,
  kEntirePort,
};

VpiPortGranularity VpiPortsReferenceGranularity(int ref_type);

VpiPortGranularity VpiPortInstReferenceGranularity(
    bool ref_is_bit_or_scalar, bool ref_is_entire_net_or_array,
    bool highconn_bit_index_undeterminable);

bool VpiPortInstReferenceQualifies(bool connected_to_any_port_bit);

std::vector<VpiHandle> VpiNetPorts(VpiHandle net);

std::vector<VpiHandle> VpiNetPortInsts(VpiHandle net);

std::vector<VpiHandle> VpiNetBitsJoinedThroughPorts(VpiHandle bit);

bool VpiIsTermOrPortRelation(int type, VpiHandle ref);
std::vector<VpiHandle> VpiTermOrPortObjects(int type, VpiHandle ref);

int VpiNetLineNo(bool implicit, int declared_line);

bool VpiIsPrimitiveType(int type);

VpiHandle VpiScopeNamedClockingBlock(VpiHandle scope, bool global);

VpiHandle VpiScopeDefaultDisableIff(VpiHandle scope);

VpiHandle VpiInstanceArrayOf(VpiHandle element, int type);

VpiHandle VpiSubobjectByIndices(VpiHandle parent, std::span<const int> indices);

bool VpiIsNetsType(int type);

bool VpiIsNetClassType(int type);

bool VpiIsBitObjectType(int type);

int VpiNetTypeOf(VpiHandle obj);
int VpiNetTypeConstant(NetType type);
const char* VpiNetTypeConstantName(int net_type);

bool VpiGetNetStrengthProperty(int property, VpiHandle obj, int& out);

int VpiResolvedNetTypeOf(VpiHandle obj);

VpiHandle VpiMergedTypedNet(VpiHandle net);

std::vector<VpiHandle> VpiModPathTerms(int type, VpiHandle path);

bool VpiHasLocationProperties(int type);

VpiHandle VpiNetBitIndex(const std::vector<VpiHandle>& indices_inner_to_outer);

std::vector<VpiHandle> VpiNetBitIndicesOutward(
    const std::vector<VpiHandle>& indices_inner_to_outer);

int VpiNetNettypeValue(bool is_part_of_nettype_net);

bool VpiNetDriverIterationSupported(int nettype_value);

std::vector<VpiHandle> VpiNetContAssigns(VpiHandle net);

int VpiInterconnectNetType();

int VpiInterconnectResolvedNetType(int simulated_resolved_type);

VpiHandle VpiNetTypespec(VpiHandle net);

bool VpiNetBitExpanded(VpiHandle net_bit);

bool VpiNetConstantSelect(bool has_parent, bool all_indices_constant,
                          bool all_elements_static_members);

struct VpiNetSizeQuery {
  int net_type = 0;
  bool packed = false;
  int bit_width = 0;
  int array_element_count = 0;
  int interconnect_array_count = 0;
  int connected_net_size = 0;
  int member_count = 0;
};

int VpiNetSize(const VpiNetSizeQuery& query);

std::vector<VpiHandle> VpiNetIndicesOutward(
    bool is_array_member, const std::vector<VpiHandle>& indices_inner_to_outer);

std::vector<VpiRangeDesc> VpiNetRanges(
    const std::vector<VpiArrayDimension>& dims);

VpiHandle VpiNetLeftRange(const std::vector<VpiArrayDimension>& dims);

VpiHandle VpiNetRightRange(const std::vector<VpiArrayDimension>& dims);

struct VpiNetScalarVectorQuery {
  int net_type = 0;
  bool has_packed_dimension = false;
  bool packed = false;
  bool base_is_scalar = false;
  bool base_is_vector = false;
  bool element_is_scalar = false;
  bool element_is_vector = false;
};

bool VpiNetScalar(const VpiNetScalarVectorQuery& query);

bool VpiNetVector(const VpiNetScalarVectorQuery& query);

bool VpiNetHasValueProperty(int net_type, bool packed_struct_union);

VpiHandle VpiNetParent(const std::vector<VpiParentPrefix>& prefixes);

bool VpiNetElementIteratorApplies(int net_type);

bool VpiIsPackedArrayNetElementType(int type);

std::vector<VpiHandle> VpiPackedArrayNetElements(VpiHandle packed_array_net);

bool VpiNetStructUnionMember(VpiHandle net);

bool VpiNetIsScalarOrVector(bool scalar, VpiHandle net);

int VpiAggregateNetSize(VpiHandle net);

std::string VpiNetName(const VpiVariableNameParts& parts);

std::string VpiNetDecompile(const VpiVariableNameParts& parts);

std::string VpiNetFullName(const VpiVariableNameParts& parts);

bool VpiIsInterconnectSubelementType(int type);

bool VpiIsInterconnectArrayDataTypespec(int typespec_type);

bool VpiIsInterconnectStructDataTypespec(int typespec_type);

int VpiInterconnectNetTypespecType(VpiHandle interconnect_net);

bool VpiIsPrimitiveArrayType(int type);

bool VpiIsInstanceArrayType(int type);

VpiHandle VpiInstanceArrayConnections(VpiHandle instance_array);

bool VpiInstanceArrayConnectionsIsListOp(VpiHandle expr);

std::vector<VpiRangeDesc> VpiInstanceArrayRanges(
    const std::vector<VpiArrayDimension>& dims);

VpiHandle VpiInstanceArrayLeftRange(const std::vector<VpiArrayDimension>& dims);

VpiHandle VpiInstanceArrayRightRange(
    const std::vector<VpiArrayDimension>& dims);

std::vector<const UdpDecl*> VpiDesignUdpDecls(const RtlirDesign* design);

void VpiFillUdpDefnObject(VpiObject* obj, const UdpDecl& decl,
                          std::deque<std::string>& names);

VpiObject* VpiUdpInitialStatement(const UdpDecl& decl, VpiObject* initial,
                                  const std::function<VpiObject*()>& alloc,
                                  std::deque<std::string>& names, Arena& arena);

void VpiFillUdpTableEntryObject(VpiObject* obj, const UdpTableRow& row,
                                VpiObject* defn, Arena& arena);

}  // namespace delta
