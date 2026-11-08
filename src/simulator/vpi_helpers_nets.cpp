#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_simple_expr_uses.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiIsInterfaceExprType(int type) {
  return type == vpiInterface || type == vpiModport ||
         type == vpiVirtualInterfaceVar || type == vpiRefObj ||
         type == vpiConstant;
}

bool VpiInterfaceExprIsValid(VpiHandle expr) {
  if (!expr) return false;
  switch (expr->type) {
    case vpiRefObj:
      return expr->actual && (expr->actual->type == vpiInterface ||
                              expr->actual->type == vpiModport);
    case vpiConstant:
      return expr->const_type == vpiNullConst;
    case vpiInterface:
    case vpiModport:
    case vpiVirtualInterfaceVar:
      return true;
    default:
      return false;
  }
}

VpiHandle VpiVirtualInterfaceExpr(VpiHandle var) {
  if (!var || var->type != vpiVirtualInterfaceVar) return nullptr;
  for (auto* child : var->children) {
    if (VpiIsInterfaceExprType(child->type) && VpiInterfaceExprIsValid(child)) {
      return child;
    }
  }
  return nullptr;
}

const char* VpiInterfaceTypespecDefName(VpiHandle interface_typespec) {
  if (!interface_typespec || interface_typespec->type != vpiInterfaceTypespec) {
    return nullptr;
  }
  return interface_typespec->def_name.empty()
             ? nullptr
             : interface_typespec->def_name.c_str();
}

VpiHandle VpiInterfaceTypespecParent(VpiHandle interface_typespec) {
  if (!interface_typespec || interface_typespec->type != vpiInterfaceTypespec) {
    return nullptr;
  }
  return interface_typespec->is_modport ? interface_typespec->parent : nullptr;
}

VpiHandle VpiClockingBlockPrefix(VpiHandle block) {
  if (!block || block->type != vpiClockingBlock) return nullptr;
  if (block->prefix != nullptr) return block->prefix;
  for (auto* child : block->children) {
    if (child->type == vpiVirtualInterfaceVar) return child;
  }
  return nullptr;
}

VpiHandle VpiClockingBlockActual(VpiHandle block) {
  if (!block || block->type != vpiClockingBlock) return nullptr;
  if (block->prefix != nullptr) return block->actual;
  VpiHandle prefix = VpiClockingBlockPrefix(block);
  if (prefix && prefix->actual == nullptr) return nullptr;
  return block->actual;
}

bool VpiIsClockingIODeclExprType(int type) {
  return type == vpiRefObj || VpiIsNetsType(type) || VpiIsVariablesType(type);
}

VpiHandle VpiClockingIODeclExpr(VpiHandle io_decl) {
  if (!io_decl || io_decl->type != vpiClockingIODecl) return nullptr;
  for (auto* child : io_decl->children) {
    if (VpiIsClockingIODeclExprType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiClockingBlockClockingEvent(VpiHandle block) {
  if (!block || block->type != vpiClockingBlock) return nullptr;
  for (auto* child : block->children) {
    if (child->type == vpiEventControl) return child;
  }
  return nullptr;
}

bool VpiIsIoDeclExprType(int type) {
  return type == vpiRefObj || type == vpiInterfaceTfDecl ||
         type == vpiVirtualInterfaceVar || VpiIsNetsType(type) ||
         type == kVpiReg;
}

int VpiIoDeclExprType(bool passed_by_reference, bool is_interface_or_modport,
                      bool is_virtual_interface, int default_expr_type) {
  if (is_virtual_interface) return vpiVirtualInterfaceVar;
  if (passed_by_reference || is_interface_or_modport) return vpiRefObj;
  return default_expr_type;
}

int VpiIoDeclDirection(int declared_direction, bool passed_by_reference,
                       bool expr_is_ref_obj_to_interface_or_modport,
                       bool expr_is_virtual_interface_var) {
  if (expr_is_ref_obj_to_interface_or_modport ||
      expr_is_virtual_interface_var) {
    return vpiNoDirection;
  }
  if (passed_by_reference) return vpiRef;
  return declared_direction;
}

VpiHandle VpiIoDeclExpr(VpiHandle io_decl) {
  if (!io_decl || io_decl->type != vpiIODecl) return nullptr;
  if (io_decl->io_expr != nullptr) return io_decl->io_expr;
  for (auto* child : io_decl->children) {
    if (VpiIsIoDeclExprType(child->type)) return child;
  }
  return nullptr;
}

std::vector<VpiRangeDesc> VpiIoDeclRanges(
    const std::vector<VpiArrayDimension>& dims) {
  return VpiTypespecRanges(dims);
}

VpiHandle VpiIoDeclLeftRange(const std::vector<VpiArrayDimension>& dims) {
  return VpiTypespecLeftRange(dims);
}

VpiHandle VpiIoDeclRightRange(const std::vector<VpiArrayDimension>& dims) {
  return VpiTypespecRightRange(dims);
}

bool VpiIsValidPortType(int port_type) {
  return port_type == vpiPort || port_type == vpiInterfacePort ||
         port_type == vpiModportPort;
}

int VpiPortTypeFromFormal(bool formal_is_interface, bool formal_is_modport) {
  if (formal_is_modport) return vpiModportPort;
  if (formal_is_interface) return vpiInterfacePort;
  return vpiPort;
}

bool VpiPortDelaysApplicable(int port_type) {
  return port_type != vpiInterfacePort;
}

VpiHandle VpiHighConn(VpiHandle obj) { return obj->high_conn; }

VpiHandle VpiLowConn(VpiHandle obj) {
  if (obj->null_port) return nullptr;
  return obj->low_conn;
}

bool VpiPortLowConnSatisfiesInterfaceRule(VpiHandle port) {
  if (!port || port->port_type != vpiInterfacePort) return true;
  return port->low_conn != nullptr && port->low_conn->type == vpiRefObj;
}

bool VpiPortScalar(int port_width) { return port_width == 1; }

bool VpiPortVector(int port_width) { return port_width > 1; }

bool VpiPortIndexAndNameApply(int type) { return type != vpiPortBit; }

const char* VpiPortName(bool explicitly_named, std::string_view explicit_name,
                        std::string_view inferred_name) {
  if (explicitly_named && !explicit_name.empty()) {
    return explicit_name.data();
  }
  if (!inferred_name.empty()) return inferred_name.data();
  return nullptr;
}

int VpiPortSize(bool is_null_port, int port_width) {
  return is_null_port ? 0 : port_width;
}

static bool VpiIsIntegralTypedNet(int net_type) {
  switch (net_type) {
    case vpiIntegerNet:
    case vpiTimeNet:
    case vpiByteNet:
    case vpiShortIntNet:
    case vpiIntNet:
    case vpiLongIntNet:
    case vpiPackedArrayNet:
      return true;
    default:
      return false;
  }
}

bool VpiIsArrayNet(int unpacked_range_count) {
  return unpacked_range_count >= 1;
}

bool VpiIsPackedArrayNet(int net_type, int explicit_packed_range_count) {
  if (explicit_packed_range_count < 1) return false;
  return net_type == vpiStructNet || net_type == vpiUnionNet ||
         net_type == vpiEnumNet;
}

bool VpiNetIsArrayMember(VpiHandle net) {
  return net != nullptr && net->parent != nullptr &&
         net->parent->type == vpiNetArray;
}

bool VpiNetIsPackedArrayMember(VpiHandle net) {
  if (!net || !net->parent || net->parent->type != vpiPackedArrayNet) {
    return false;
  }
  switch (net->type) {
    case vpiStructNet:
    case vpiUnionNet:
    case vpiEnumNet:
    case vpiPackedArrayNet:
      return true;
    default:
      return false;
  }
}

bool VpiNetBitIteratorApplies(int net_type) {
  return net_type == vpiNet || net_type == vpiBitNet;
}

bool VpiNetTerminalAccessAllowed(bool is_scalar_net_or_bit_select) {
  return is_scalar_net_or_bit_select;
}

VpiPortGranularity VpiPortsReferenceGranularity(int ref_type) {
  if (ref_type == vpiNetBit) return VpiPortGranularity::kPortBits;
  return VpiPortGranularity::kEntirePort;
}

VpiPortGranularity VpiPortInstReferenceGranularity(
    bool ref_is_bit_or_scalar, bool ref_is_entire_net_or_array,
    bool highconn_bit_index_undeterminable) {
  if (ref_is_entire_net_or_array) return VpiPortGranularity::kEntirePort;
  if (ref_is_bit_or_scalar) {
    return highconn_bit_index_undeterminable ? VpiPortGranularity::kEntirePort
                                             : VpiPortGranularity::kPortBits;
  }
  return VpiPortGranularity::kEntirePort;
}

bool VpiPortInstReferenceQualifies(bool connected_to_any_port_bit) {
  return connected_to_any_port_bit;
}

int VpiNetLineNo(bool implicit, int declared_line) {
  return implicit ? 0 : declared_line;
}

bool VpiHasLocationProperties(int type) {
  switch (type) {
    case vpiCallback:
    case vpiDelayTerm:
    case vpiDelayDevice:
    case vpiInterModPath:
    case vpiIterator:
    case vpiTimeQueue:
    case vpiGenScopeArray:
    case vpiGenScope:
      return false;
    default:
      return true;
  }
}

VpiHandle VpiNetBitIndex(const std::vector<VpiHandle>& indices_inner_to_outer) {
  if (indices_inner_to_outer.empty()) return nullptr;
  return indices_inner_to_outer.front();
}

std::vector<VpiHandle> VpiNetBitIndicesOutward(
    const std::vector<VpiHandle>& indices_inner_to_outer) {
  return indices_inner_to_outer;
}

int VpiNetNettypeValue(bool is_part_of_nettype_net) {
  return is_part_of_nettype_net ? vpiNettypeNetSelect : vpiNettypeNet;
}

bool VpiNetDriverIterationSupported(int nettype_value) {
  return nettype_value != vpiNettypeNetSelect;
}

std::vector<VpiHandle> VpiNetContAssigns(VpiHandle net) {
  std::vector<VpiHandle> assigns;
  const bool kBit = net->type == vpiNetBit;
  const VpiObject* holder = kBit ? net->parent : net;
  if (holder == nullptr) return assigns;
  if (!kBit && std::ranges::any_of(net->children, [](const VpiObject* child) {
        return child->type == vpiNetBit;
      })) {
    return assigns;
  }
  for (VpiObject* child : holder->children) {
    if (child->type == vpiContAssign && (!kBit || VpiUsesExpr(*child, *net))) {
      assigns.push_back(child);
    }
  }
  return assigns;
}

int VpiInterconnectNetType() { return vpiInterconnect; }

int VpiInterconnectResolvedNetType(int simulated_resolved_type) {
  return simulated_resolved_type;
}

VpiHandle VpiNetTypespec(VpiHandle net) {
  if (!net || net->type == vpiInterconnectArray) return nullptr;
  for (auto* child : net->children) {
    if (child->type == vpiTypespec) return child;
  }
  return nullptr;
}

bool VpiNetBitExpanded(VpiHandle net_bit) {
  if (!net_bit->parent) return true;
  return !net_bit->parent->is_vectored;
}

bool VpiNetConstantSelect(bool has_parent, bool all_indices_constant,
                          bool all_elements_static_members) {
  if (!has_parent) return true;
  return all_indices_constant && all_elements_static_members;
}

int VpiNetSize(const VpiNetSizeQuery& query) {
  switch (query.net_type) {
    case vpiInterconnectArray:
      return query.interconnect_array_count;
    case vpiInterconnectNet:
      return query.connected_net_size;
    case vpiNetArray:
      return query.array_element_count;
    case vpiNetBit:
      return 1;
    case vpiStructNet:
    case vpiUnionNet:
      return query.packed ? query.bit_width : query.member_count;
    default:
      break;
  }
  if (VpiIsIntegralTypedNet(query.net_type) || query.net_type == vpiNet ||
      query.net_type == vpiBitNet || query.net_type == vpiEnumNet) {
    return query.bit_width;
  }
  return 0;
}

std::vector<VpiHandle> VpiNetIndicesOutward(
    bool is_array_member,
    const std::vector<VpiHandle>& indices_inner_to_outer) {
  if (!is_array_member) return {};
  return indices_inner_to_outer;
}

std::vector<VpiRangeDesc> VpiNetRanges(
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

static VpiRangeDesc LeftmostNetRange(
    const std::vector<VpiArrayDimension>& dims) {
  std::vector<VpiRangeDesc> ranges = VpiNetRanges(dims);
  if (ranges.empty()) {
    VpiRangeDesc empty;
    empty.empty = true;
    return empty;
  }
  return ranges.front();
}

VpiHandle VpiNetLeftRange(const std::vector<VpiArrayDimension>& dims) {
  return VpiRangeLeftRange(LeftmostNetRange(dims));
}

VpiHandle VpiNetRightRange(const std::vector<VpiArrayDimension>& dims) {
  return VpiRangeRightRange(LeftmostNetRange(dims));
}

bool VpiNetScalar(const VpiNetScalarVectorQuery& query) {
  if (query.net_type == vpiNet || query.net_type == vpiBitNet) {
    return !query.has_packed_dimension;
  }
  if (query.net_type == vpiNetBit) return true;
  if (query.net_type == vpiEnumNet) return query.base_is_scalar;
  if (query.net_type == vpiNetArray) return query.element_is_scalar;
  return false;
}

bool VpiNetVector(const VpiNetScalarVectorQuery& query) {
  if (query.net_type == vpiNet || query.net_type == vpiBitNet) {
    return query.has_packed_dimension;
  }
  if (query.net_type == vpiNetBit) return false;
  if (query.net_type == vpiEnumNet) return query.base_is_vector;
  if (query.net_type == vpiStructNet || query.net_type == vpiUnionNet) {
    return query.packed;
  }
  if (query.net_type == vpiNetArray) return query.element_is_vector;
  return VpiIsIntegralTypedNet(query.net_type);
}

bool VpiNetHasValueProperty(int net_type, bool packed_struct_union) {
  if (net_type == vpiNetArray || net_type == vpiInterconnectArray) return false;
  if ((net_type == vpiStructNet || net_type == vpiUnionNet) &&
      !packed_struct_union) {
    return false;
  }
  return true;
}

VpiHandle VpiNetParent(const std::vector<VpiParentPrefix>& prefixes) {
  for (const auto& prefix : prefixes) {
    if (prefix.qualifies) return prefix.handle;
  }
  return nullptr;
}

bool VpiNetElementIteratorApplies(int net_type) {
  return net_type == vpiPackedArrayNet;
}

std::vector<VpiHandle> VpiPackedArrayNetElements(VpiHandle packed_array_net) {
  if (!packed_array_net ||
      !VpiNetElementIteratorApplies(packed_array_net->type)) {
    return {};
  }
  return packed_array_net->children;
}

bool VpiNetStructUnionMember(VpiHandle net) {
  if (net->type == vpiNetBit || !net->parent) return false;
  return net->parent->type == vpiStructNet || net->parent->type == vpiUnionNet;
}

std::string VpiNetName(const VpiVariableNameParts& parts) {
  return parts.member + parts.index_suffix;
}

std::string VpiNetDecompile(const VpiVariableNameParts& parts) {
  std::string result;
  for (const auto& prefix : parts.member_prefixes) {
    result += prefix + ".";
  }
  result += parts.member + parts.index_suffix;
  return result;
}

std::string VpiNetFullName(const VpiVariableNameParts& parts) {
  std::string decompile = VpiNetDecompile(parts);
  if (parts.top_scope.empty()) return decompile;
  return parts.top_scope + "." + decompile;
}

bool VpiIsInterconnectSubelementType(int type) {
  return type == vpiInterconnectArray || type == vpiInterconnectNet;
}

bool VpiIsInterconnectArrayDataTypespec(int typespec_type) {
  return typespec_type == vpiArrayTypespec ||
         typespec_type == vpiPackedArrayTypespec;
}

bool VpiIsInterconnectStructDataTypespec(int typespec_type) {
  return typespec_type == vpiStructTypespec ||
         typespec_type == vpiUnionTypespec;
}

int VpiInterconnectNetTypespecType(VpiHandle interconnect_net) {
  for (auto* child : interconnect_net->children) {
    if (VpiIsTypespecType(child->type)) return child->type;
  }
  return 0;
}

bool VpiIsPrimitiveArrayType(int type) {
  switch (type) {
    case vpiPrimitiveArray:
    case vpiGateArray:
    case vpiSwitchArray:
    case vpiUdpArray:
      return true;
    default:
      return false;
  }
}

bool VpiIsNetsType(int type) {
  switch (type) {
    case kVpiNet:
    case vpiNetBit:
    case vpiNetArray:
    case vpiStructNet:
    case vpiUnionNet:
    case vpiEnumNet:
    case vpiIntegerNet:
    case vpiTimeNet:
    case vpiBitNet:
    case vpiByteNet:
    case vpiShortIntNet:
    case vpiIntNet:
    case vpiLongIntNet:
    case vpiRealNet:
    case vpiShortRealNet:
    case vpiPackedArrayNet:
    case vpiInterconnectNet:
    case vpiInterconnectArray:
      return true;
    default:
      return false;
  }
}

bool VpiIsNetClassType(int type) {
  return VpiIsNetsType(type) && type != vpiNetBit && type != vpiNetArray &&
         type != vpiInterconnectArray;
}

bool VpiIsBitObjectType(int type) {
  return type == vpiPortBit || type == vpiNetBit || type == vpiRegBit ||
         type == vpiContAssignBit;
}

static bool VpiModPathTermMatches(int type, VpiHandle term) {
  const bool kIsOut = term->direction == kVpiOutput;
  if (type == vpiModPathOut) return kIsOut;
  if (kIsOut) return false;
  return type == vpiModDataPathIn ? term->data_path_term
                                  : !term->data_path_term;
}

std::vector<VpiHandle> VpiModPathTerms(int type, VpiHandle path) {
  std::vector<VpiHandle> terms;
  for (auto* child : path->children) {
    if (child->type != vpiPathTerm) continue;
    if (VpiModPathTermMatches(type, child)) terms.push_back(child);
  }
  return terms;
}

bool VpiIsInstanceArrayType(int type) {
  switch (type) {
    case vpiInstanceArray:
    case vpiModuleArray:
    case vpiInterfaceArray:
    case vpiProgramArray:
      return true;
    default:
      return VpiIsPrimitiveArrayType(type);
  }
}

VpiHandle VpiInstanceArrayConnections(VpiHandle instance_array) {
  if (!instance_array) return nullptr;
  if (!VpiIsInstanceArrayType(instance_array->type)) return nullptr;
  for (auto* child : instance_array->children) {
    if (child->type == vpiOperation) return child;
  }
  return nullptr;
}

bool VpiInstanceArrayConnectionsIsListOp(VpiHandle expr) {
  return expr && expr->type == vpiOperation && expr->op_type == vpiListOp;
}

std::vector<VpiRangeDesc> VpiInstanceArrayRanges(
    const std::vector<VpiArrayDimension>& dims) {
  std::vector<VpiRangeDesc> ranges;
  for (const auto& dim : dims) {
    VpiRangeDesc range;
    range.empty = VpiDimensionRangeIsEmpty(dim.kind);
    range.left_expr = dim.left_expr;
    range.right_expr = dim.right_expr;
    range.size = dim.size;
    ranges.push_back(range);
  }
  return ranges;
}

static VpiRangeDesc LeftmostInstanceArrayRange(
    const std::vector<VpiArrayDimension>& dims) {
  std::vector<VpiRangeDesc> ranges = VpiInstanceArrayRanges(dims);
  if (ranges.empty()) {
    VpiRangeDesc empty;
    empty.empty = true;
    return empty;
  }
  return ranges.front();
}

VpiHandle VpiInstanceArrayLeftRange(
    const std::vector<VpiArrayDimension>& dims) {
  return VpiRangeLeftRange(LeftmostInstanceArrayRange(dims));
}

VpiHandle VpiInstanceArrayRightRange(
    const std::vector<VpiArrayDimension>& dims) {
  return VpiRangeRightRange(LeftmostInstanceArrayRange(dims));
}

}  // namespace delta
