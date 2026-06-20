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
#include "simulator/vpi.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"

namespace delta {

bool VpiIsInterfaceExprType(int type) {
  // §37.29 (figure, "interface expr" group): the object kinds that may sit at
  // the far end of a virtual interface var's vpiExpr - an interface, a modport,
  // another virtual interface var, a ref obj, or a constant.
  return type == vpiInterface || type == vpiModport ||
         type == vpiVirtualInterfaceVar || type == vpiRefObj ||
         type == vpiConstant;
}

bool VpiInterfaceExprIsValid(VpiHandle expr) {
  // §37.29 detail 2: not every object of an interface-expr kind is a legal
  // interface expr. A ref obj qualifies only when it is a local declaration of
  // an interface or modport passed through a port - observable as its vpiActual
  // being an interface or a modport. A constant qualifies only when its
  // vpiConstType is vpiNullConst. An interface, a modport, or a virtual
  // interface var always qualifies.
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
  // §37.29 detail 1: vpiExpr of a virtual interface var reaches the interface
  // instance assigned to it in its declaration, if any; otherwise NULL. The
  // assignment is modeled as the first child that is a legal interface expr,
  // so a child of an interface-expr kind that fails the detail-2 constraint is
  // not an interface expr and is not handed back.
  if (!var || var->type != vpiVirtualInterfaceVar) return nullptr;
  for (auto* child : var->children) {
    if (VpiIsInterfaceExprType(child->type) && VpiInterfaceExprIsValid(child)) {
      return child;
    }
  }
  return nullptr;
}

// ===========================================================================
// §37.30 Interface typespec.
// ===========================================================================

const char* VpiInterfaceTypespecDefName(VpiHandle interface_typespec) {
  // §37.30 detail 1: a modport interface typespec reports the modport
  // identifier as its vpiDefName, and an interface interface typespec reports
  // the interface declaration's identifier. Either definition name is held on
  // the typespec, so it is handed back directly; a typespec with no recorded
  // definition name, or a handle of any other kind, yields NULL.
  if (!interface_typespec || interface_typespec->type != vpiInterfaceTypespec) {
    return nullptr;
  }
  return interface_typespec->def_name.empty()
             ? nullptr
             : interface_typespec->def_name.c_str();
}

VpiHandle VpiInterfaceTypespecParent(VpiHandle interface_typespec) {
  // §37.30 detail 2: a modport interface typespec's vpiParent is the interface
  // typespec of the interface it belongs to; an interface interface typespec
  // has no parent, so it reports NULL even when some enclosing object exists.
  if (!interface_typespec || interface_typespec->type != vpiInterfaceTypespec) {
    return nullptr;
  }
  return interface_typespec->is_modport ? interface_typespec->parent : nullptr;
}

// ===========================================================================
// §37.48 Clocking block.
// ===========================================================================

VpiHandle VpiClockingBlockPrefix(VpiHandle block) {
  // §37.48 detail 2: vpiPrefix of a clocking block is non-NULL exactly when the
  // clocking block names an expression immediately prefixed by a virtual
  // interface (for example "vif.cb"). That prefix - the virtual interface var -
  // is modeled as a virtual interface var child. A clocking block that is not
  // so prefixed has no such child, so the relation reports NULL. The generic
  // walk cannot serve this transition: vpiPrefix and vpiVirtualInterfaceVar are
  // different type tags, so the prefix child is only found here.
  if (!block || block->type != vpiClockingBlock) return nullptr;
  for (auto* child : block->children) {
    if (child->type == vpiVirtualInterfaceVar) return child;
  }
  return nullptr;
}

VpiHandle VpiClockingBlockActual(VpiHandle block) {
  // §37.48 detail 3: vpiActual of a clocking block reaches the concrete
  // clocking block selected through its virtual interface prefix, held on the
  // designated actual pointer. When the prefix is a virtual interface that has
  // no value at the current simulation time - its own vpiActual being NULL,
  // exactly as a virtual interface var is left uninitialized in §37.29 - the
  // clocking block's vpiActual is NULL as well, regardless of any resolved
  // actual.
  if (!block || block->type != vpiClockingBlock) return nullptr;
  VpiHandle prefix = VpiClockingBlockPrefix(block);
  if (prefix && prefix->actual == nullptr) return nullptr;
  return block->actual;
}

bool VpiIsClockingIODeclExprType(int type) {
  // §37.48 (figure, clocking io decl -> nets / variables / ref obj): the object
  // kinds a clocking io decl's vpiExpr relation may reach. As in §37.13's io
  // decl, the named target is a net, a variable (a logic var shares vpiReg's
  // code), or a ref obj.
  return type == vpiRefObj || type == kVpiNet || type == kVpiReg ||
         type == vpiVariables || VpiIsLogicVarType(type);
}

VpiHandle VpiClockingIODeclExpr(VpiHandle io_decl) {
  // §37.48 detail 4: vpiExpr of a clocking io decl reaches the expression or
  // ref obj the io decl names. For "enable = top.mem1.enable" the io decl
  // "enable" reaches a handle to the ref obj "top.mem1.enable". The named
  // object is modeled as the first child of a net / variable / ref obj kind;
  // the io decl's other children (its input/output skews) are not the named
  // expression. The generic walk cannot serve this transition because vpiExpr
  // and the named object carry different type tags.
  if (!io_decl || io_decl->type != vpiClockingIODecl) return nullptr;
  for (auto* child : io_decl->children) {
    if (VpiIsClockingIODeclExprType(child->type)) return child;
  }
  return nullptr;
}

// ===========================================================================
// §37.13 IO declaration.
// ===========================================================================

bool VpiIsIoDeclExprType(int type) {
  // §37.13: the object kinds the io decl's vpiExpr relation draws to - the
  // named ref obj / interface tf decl / virtual interface var target boxes plus
  // the nets and variables groupings (a logic var shares vpiReg's code).
  return type == vpiRefObj || type == vpiInterfaceTfDecl ||
         type == vpiVirtualInterfaceVar || type == kVpiNet || type == kVpiReg;
}

int VpiIoDeclExprType(bool passed_by_reference, bool is_interface_or_modport,
                      bool is_virtual_interface, int default_expr_type) {
  // §37.13 detail 2: a virtual-interface io decl resolves to its virtual
  // interface var; an io decl passed by reference, or one that is an interface
  // or a modport, resolves to a ref obj. Anything else keeps the directly
  // connected expression kind the caller already knows.
  if (is_virtual_interface) return vpiVirtualInterfaceVar;
  if (passed_by_reference || is_interface_or_modport) return vpiRefObj;
  return default_expr_type;
}

int VpiIoDeclDirection(int declared_direction, bool passed_by_reference,
                       bool expr_is_ref_obj_to_interface_or_modport,
                       bool expr_is_virtual_interface_var) {
  // §37.13 detail 3 first: an io decl whose vpiExpr denotes an
  // interface/modport (through a ref obj) or a virtual interface var has no
  // defined direction.
  if (expr_is_ref_obj_to_interface_or_modport ||
      expr_is_virtual_interface_var) {
    return vpiNoDirection;
  }
  // §37.13 detail 1: a port or argument passed by reference reports vpiRef.
  if (passed_by_reference) return vpiRef;
  return declared_direction;
}

VpiHandle VpiIoDeclExpr(VpiHandle io_decl) {
  // §37.13 detail 2: vpiExpr of an io decl reaches a single designated
  // connection whose own type is an expr-target kind rather than vpiExpr, so
  // the first such child is the relation's target.
  if (!io_decl || io_decl->type != vpiIODecl) return nullptr;
  for (auto* child : io_decl->children) {
    if (VpiIsIoDeclExprType(child->type)) return child;
  }
  return nullptr;
}

std::vector<VpiRangeDesc> VpiIoDeclRanges(
    const std::vector<VpiArrayDimension>& dims) {
  // §37.13 detail 4: the io decl's vpiRange iteration is the same as for its
  // corresponding typespec (§37.25).
  return VpiTypespecRanges(dims);
}

VpiHandle VpiIoDeclLeftRange(const std::vector<VpiArrayDimension>& dims) {
  // §37.13 detail 4: vpiLeftRange is the corresponding typespec's vpiLeftRange.
  return VpiTypespecLeftRange(dims);
}

VpiHandle VpiIoDeclRightRange(const std::vector<VpiArrayDimension>& dims) {
  // §37.13 detail 4: vpiRightRange is the corresponding typespec's
  // vpiRightRange.
  return VpiTypespecRightRange(dims);
}

// ===========================================================================
// §37.14 Ports and §37.15 Reference objects.
// ===========================================================================

bool VpiIsValidPortType(int port_type) {
  // §37.14 detail 1: a port's vpiPortType is one of exactly these three values.
  return port_type == vpiPort || port_type == vpiInterfacePort ||
         port_type == vpiModportPort;
}

int VpiPortTypeFromFormal(bool formal_is_interface, bool formal_is_modport) {
  // §37.14 detail 1: the port type follows the formal. A modport formal makes a
  // modport port, an interface formal an interface port, and anything else an
  // ordinary port. The actual the port connects to is never consulted.
  if (formal_is_modport) return vpiModportPort;
  if (formal_is_interface) return vpiInterfacePort;
  return vpiPort;
}

bool VpiPortDelaysApplicable(int port_type) {
  // §37.14 detail 2: the delay routines do not apply to an interface port.
  return port_type != vpiInterfacePort;
}

VpiHandle VpiHighConn(VpiHandle obj) {
  // §37.14 details 3 and 10 (shared with §37.15): the higher connection, or
  // NULL when the instance has no connection to the port. A null pointer
  // already encodes "no connection", so it is handed straight back.
  if (!obj) return nullptr;
  return obj->high_conn;
}

VpiHandle VpiLowConn(VpiHandle obj) {
  // §37.14 details 4 and 10 (shared with §37.15): the lower connection. A null
  // port carries no low connection, so its stored pointer is NULL.
  if (!obj) return nullptr;
  if (obj->null_port) return nullptr;
  return obj->low_conn;
}

bool VpiPortLowConnSatisfiesInterfaceRule(VpiHandle port) {
  // §37.14 detail 5: an interface port's lowConn must always be a ref obj
  // (§37.15). For any other port type the rule does not constrain the lowConn.
  if (!port || port->port_type != vpiInterfacePort) return true;
  return port->low_conn != nullptr && port->low_conn->type == vpiRefObj;
}

bool VpiPortScalar(int port_width) {
  // §37.14 detail 6: a port is scalar when it is exactly one bit wide. This
  // reflects the port itself, not whatever is connected to it.
  return port_width == 1;
}

bool VpiPortVector(int port_width) {
  // §37.14 detail 6: a port is a vector when it is more than one bit wide.
  return port_width > 1;
}

bool VpiPortIndexAndNameApply(int type) {
  // §37.14 detail 7: vpiPortIndex and vpiName apply to a whole port but not to
  // a port bit.
  return type != vpiPortBit;
}

const char* VpiPortName(bool explicitly_named, const char* explicit_name,
                        const char* inferred_name) {
  // §37.14 detail 8: an explicitly named port returns its explicit name;
  // failing that, an inferred name is returned if one exists; otherwise NULL.
  if (explicitly_named && explicit_name && explicit_name[0] != '\0') {
    return explicit_name;
  }
  if (inferred_name && inferred_name[0] != '\0') return inferred_name;
  return nullptr;
}

int VpiPortSize(bool is_null_port, int port_width) {
  // §37.14 detail 11: a null port has size 0; otherwise the size is the port's
  // bit width.
  return is_null_port ? 0 : port_width;
}

int VpiRefObjGeneric(bool refers_to_interface, bool is_generic_interface) {
  // §37.15 detail 5: a ref obj that refers to an interface reports whether that
  // interface is generic; any other ref obj reports vpiUndefined.
  if (!refers_to_interface) return vpiUndefined;
  return is_generic_interface ? 1 : 0;
}

// §37.15 detail 6: the actual kinds whose definition/modport name a ref obj's
// vpiDefName reports - an interface, an interface array, or a modport.
static bool VpiRefObjActualIsInterfaceOrModport(int actual_type) {
  return actual_type == vpiInterface || actual_type == vpiInterfaceArray ||
         actual_type == vpiModport;
}

const char* VpiRefObjDefName(VpiHandle ref_obj) {
  // §37.15 detail 6: when the ref obj's actual is an interface or modport, its
  // definition name (or the modport name) is reported; otherwise there is none.
  if (!ref_obj || !ref_obj->actual) return nullptr;
  if (!VpiRefObjActualIsInterfaceOrModport(ref_obj->actual->type)) {
    return nullptr;
  }
  return ref_obj->actual->name.data();
}

// §37.15 detail 7: the actual kinds that carry a typespec - a net, a variable,
// or a part select. A ref obj bound to any of these exposes vpiTypespec; bound
// to anything else (an interface, modport, named event, ...) it does not.
static bool VpiRefObjActualHasTypespec(int actual_type) {
  switch (actual_type) {
    case vpiNet:  // == kVpiNet, the net family head
    case vpiStructNet:
    case vpiUnionNet:
    case vpiEnumNet:
    case vpiIntegerNet:
    case vpiTimeNet:
    case vpiBitNet:
    case vpiPackedArrayNet:
    case vpiReg:  // == vpiLogicVar, the variable family head
    case vpiIntegerVar:
    case vpiRealVar:
    case vpiIntVar:
    case vpiBitVar:
    case vpiPartSelect:
      return true;
    default:
      return false;
  }
}

VpiHandle VpiRefObjTypespec(VpiHandle ref_obj) {
  // §37.15 detail 7: NULL unless the ref obj's actual is a net, variable, or
  // part select; in that case the ref obj's own typespec child is returned.
  if (!ref_obj || !ref_obj->actual) return nullptr;
  if (!VpiRefObjActualHasTypespec(ref_obj->actual->type)) return nullptr;
  for (auto* child : ref_obj->children) {
    if (child->type == vpiTypespec) return child;
  }
  return nullptr;
}

// ===========================================================================
// §37.16 Nets.
// ===========================================================================

// §37.16: the net object kinds the simulator's data type can hold. An
// integral-typed net is one whose value is a packed vector of bits
// (see 6.11.1); enum, logic, and bit nets are handled separately by the
// scalar/vector rules.
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
  // §37.16 detail 1: one or more unpacked ranges makes a net an array net.
  return unpacked_range_count >= 1;
}

bool VpiIsPackedArrayNet(int net_type, int explicit_packed_range_count) {
  // §37.16 detail 1: a packed struct/union net or an enum net becomes a packed
  // array net when it carries at least one explicit packed range.
  if (explicit_packed_range_count < 1) return false;
  return net_type == vpiStructNet || net_type == vpiUnionNet ||
         net_type == vpiEnumNet;
}

bool VpiNetIsArrayMember(VpiHandle net) {
  // §37.16 detail 2: a net is an array member when its vpiParent prefix is an
  // array net.
  return net != nullptr && net->parent != nullptr &&
         net->parent->type == vpiNetArray;
}

bool VpiNetIsPackedArrayMember(VpiHandle net) {
  // §37.16 detail 2: vpiPackedArrayMember is TRUE for a packed struct/union
  // net, an enum net, or a packed array net whose vpiParent prefix is a packed
  // array net.
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
  // §37.16 detail 3: a logic net or bit net always exposes its net bits,
  // whether or not the vector was expanded.
  return net_type == vpiNet || net_type == vpiBitNet;
}

bool VpiNetTerminalAccessAllowed(bool is_scalar_net_or_bit_select) {
  // §37.16 detail 5: continuous assignments and primitive terminals are
  // reachable only from a scalar net or a bit-select.
  return is_scalar_net_or_bit_select;
}

VpiPortGranularity VpiPortsReferenceGranularity(int ref_type) {
  // §37.16 detail 6: a net bit reference selects the matching port bits; an
  // entire net or array net reference selects a handle to the whole port.
  if (ref_type == vpiNetBit) return VpiPortGranularity::kPortBits;
  return VpiPortGranularity::kEntirePort;
}

VpiPortGranularity VpiPortInstReferenceGranularity(
    bool ref_is_bit_or_scalar, bool ref_is_entire_net_or_array,
    bool highconn_bit_index_undeterminable) {
  // §37.16 detail 7: an entire net or array net reference always selects the
  // whole port. A bit or scalar reference selects the matching port bits or
  // scalar ports, except when the highconn is a complex expression whose bit
  // index cannot be determined - then the whole port is selected instead.
  if (ref_is_entire_net_or_array) return VpiPortGranularity::kEntirePort;
  if (ref_is_bit_or_scalar) {
    return highconn_bit_index_undeterminable ? VpiPortGranularity::kEntirePort
                                             : VpiPortGranularity::kPortBits;
  }
  return VpiPortGranularity::kEntirePort;
}

bool VpiPortInstReferenceQualifies(bool connected_to_any_port_bit) {
  // §37.16 detail 8: a reference inside the highconn that is connected to none
  // of the port's bits does not qualify as a member of the iteration.
  return connected_to_any_port_bit;
}

int VpiNetLineNo(bool implicit, int declared_line) {
  // §37.16 detail 9: an implicit net has no declaration line, so vpiLineNo is
  // 0.
  return implicit ? 0 : declared_line;
}

bool VpiHasLocationProperties(int type) {
  // §37.3.3: vpiLineNo and vpiFile apply to every object that maps to source
  // text. The exceptions are object kinds that have no single source line or
  // file; for those the location properties are not valid queries.
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
  // §37.16 detail 10: the bit index of a net bit is its single innermost index.
  if (indices_inner_to_outer.empty()) return nullptr;
  return indices_inner_to_outer.front();
}

std::vector<VpiHandle> VpiNetBitIndicesOutward(
    const std::vector<VpiHandle>& indices_inner_to_outer) {
  // §37.16 detail 10: a multidimensional net array bit-select iterates from the
  // net bit's index outward, the order the inputs already carry.
  return indices_inner_to_outer;
}

int VpiNetNettypeValue(bool is_part_of_nettype_net) {
  // §37.16 detail 11: a select of a nettype net reports vpiNettypeNetSelect; a
  // net not declared with a nettype reports vpiNettypeNet.
  return is_part_of_nettype_net ? vpiNettypeNetSelect : vpiNettypeNet;
}

bool VpiNetDriverIterationSupported(int nettype_value) {
  // §37.16 detail 11: driver iteration is unsupported on a vpiNettypeNetSelect.
  return nettype_value != vpiNettypeNetSelect;
}

int VpiInterconnectNetType() {
  // §37.16 detail 12: an interconnect net or interconnect net select reports
  // vpiInterconnect.
  return vpiInterconnect;
}

int VpiInterconnectResolvedNetType(int simulated_resolved_type) {
  // §37.16 detail 12: a simulated interconnect net resolves to the type of the
  // simulated net (see 23.3.3.7).
  return simulated_resolved_type;
}

VpiHandle VpiNetTypespec(VpiHandle net) {
  // §37.16 detail 13: an interconnect array has no typespec; any other net
  // hands back its first typespec child.
  if (!net || net->type == vpiInterconnectArray) return nullptr;
  for (auto* child : net->children) {
    if (child->type == vpiTypespec) return child;
  }
  return nullptr;
}

bool VpiNetBitExpanded(VpiHandle net_bit) {
  // §37.16 detail 21: vpiExpanded on a net bit reports the parent net's value.
  // A scalared net (and the default) is expanded; a vectored net is not.
  if (!net_bit || !net_bit->parent) return true;
  return !net_bit->parent->is_vectored;
}

bool VpiNetConstantSelect(bool has_parent, bool all_indices_constant,
                          bool all_elements_static_members) {
  // §37.16 detail 23: a net or net bit with no parent is a constant select, as
  // is a select whose indices are all elaboration-time constants and whose
  // elements are all struct/union net members or static-bound array elements.
  if (!has_parent) return true;
  return all_indices_constant && all_elements_static_members;
}

int VpiNetSize(const VpiNetSizeQuery& query) {
  // §37.16 detail 24: vpiSize depends on the kind of net.
  switch (query.net_type) {
    case vpiInterconnectArray:
      return query.interconnect_array_count;
    case vpiInterconnectNet:
      return query.connected_net_size;  // the connected net's size
    case vpiNetArray:
      return query.array_element_count;  // number of nets in the array
    case vpiNetBit:
      return 1;
    case vpiStructNet:
    case vpiUnionNet:
      // packed -> integral, size in bits; unpacked -> number of members
      return query.packed ? query.bit_width : query.member_count;
    default:
      break;
  }
  if (VpiIsIntegralTypedNet(query.net_type) || query.net_type == vpiNet ||
      query.net_type == vpiBitNet || query.net_type == vpiEnumNet) {
    return query.bit_width;  // net of an integral data type -> size in bits
  }
  return 0;  // vpiSize not defined for any other net
}

std::vector<VpiHandle> VpiNetIndicesOutward(
    bool is_array_member,
    const std::vector<VpiHandle>& indices_inner_to_outer) {
  // §37.16 detail 25: only an element of an array net has an index iteration;
  // it runs from the net's own index outward. A net that is not an array
  // element yields no indices.
  if (!is_array_member) return {};
  return indices_inner_to_outer;
}

std::vector<VpiRangeDesc> VpiNetRanges(
    const std::vector<VpiArrayDimension>& dims) {
  // §37.16 detail 26 (woven with §37.22): one range per declared dimension, in
  // declaration order. Each dimension routes through §37.22's empty-range rule;
  // the implicit element ranges of a packed struct/union element are dropped
  // (detail 1).
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

// §37.16 detail 26: the §37.22 range for a net's leftmost packed dimension, the
// one vpiLeftRange/vpiRightRange report. Returns an empty range (so both
// relations yield NULL) when the net has no dimensions.
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
  // §37.16 detail 26: defer to §37.22's vpiLeftRange.
  return VpiRangeLeftRange(LeftmostNetRange(dims));
}

VpiHandle VpiNetRightRange(const std::vector<VpiArrayDimension>& dims) {
  // §37.16 detail 26: the mirror of VpiNetLeftRange.
  return VpiRangeRightRange(LeftmostNetRange(dims));
}

bool VpiNetScalar(const VpiNetScalarVectorQuery& query) {
  // §37.16 detail 28: a bit/logic net with no packed dimension and a net bit
  // are scalars; an enum net defers to its base typespec; an array net defers
  // to an element; every other net is not a scalar.
  if (query.net_type == vpiNet || query.net_type == vpiBitNet) {
    return !query.has_packed_dimension;
  }
  if (query.net_type == vpiNetBit) return true;
  if (query.net_type == vpiEnumNet) return query.base_is_scalar;
  if (query.net_type == vpiNetArray) return query.element_is_scalar;
  return false;
}

bool VpiNetVector(const VpiNetScalarVectorQuery& query) {
  // §37.16 detail 28: a bit/logic net with a packed dimension, the
  // integral-typed nets, and a packed struct/union net are vectors; an enum net
  // defers to its base typespec; an array net defers to an element; every other
  // net is not a vector.
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
  // §37.16 detail 30: array nets, unpacked struct/union nets, and interconnect
  // arrays have no value property; every other net does.
  if (net_type == vpiNetArray || net_type == vpiInterconnectArray) return false;
  if ((net_type == vpiStructNet || net_type == vpiUnionNet) &&
      !packed_struct_union) {
    return false;
  }
  return true;
}

VpiHandle VpiNetParent(const std::vector<VpiParentPrefix>& prefixes) {
  // §37.16 detail 31: scan the prefixes rightmost to leftmost and return the
  // first one that qualifies; NULL when none does.
  for (const auto& prefix : prefixes) {
    if (prefix.qualifies) return prefix.handle;
  }
  return nullptr;
}

bool VpiNetElementIteratorApplies(int net_type) {
  // §37.16 detail 32: vpiElement iterates only over a packed array net.
  return net_type == vpiPackedArrayNet;
}

std::vector<VpiHandle> VpiPackedArrayNetElements(VpiHandle packed_array_net) {
  // §37.16 detail 32: the subelements of a packed array net are its element
  // children, returned in declaration order. A net that is not a packed array
  // net has none.
  if (!packed_array_net ||
      !VpiNetElementIteratorApplies(packed_array_net->type)) {
    return {};
  }
  return packed_array_net->children;
}

bool VpiNetStructUnionMember(VpiHandle net) {
  // §37.16 detail 33: TRUE for a net or array net whose vpiParent is a struct
  // or union net; not defined for a net bit (whose vpiParent is a net),
  // reported FALSE.
  if (!net || net->type == vpiNetBit || !net->parent) return false;
  return net->parent->type == vpiStructNet || net->parent->type == vpiUnionNet;
}

std::string VpiNetName(const VpiVariableNameParts& parts) {
  // §37.16 detail 34: the leaf member with its own index/slice, no prefixes.
  return parts.member + parts.index_suffix;
}

std::string VpiNetDecompile(const VpiVariableNameParts& parts) {
  // §37.16 detail 34: the struct/union-net prefixes joined to the member (with
  // its index/slice), without the top-level scope.
  std::string result;
  for (const auto& prefix : parts.member_prefixes) {
    result += prefix + ".";
  }
  result += parts.member + parts.index_suffix;
  return result;
}

std::string VpiNetFullName(const VpiVariableNameParts& parts) {
  // §37.16 detail 34: the top-level scope prefixed to the decompile form.
  std::string decompile = VpiNetDecompile(parts);
  if (parts.top_scope.empty()) return decompile;
  return parts.top_scope + "." + decompile;
}

// ===========================================================================
// §37.24 Generic interconnect.
//
// The generic-interconnect data model draws an interconnect array and the
// interconnect nets it ultimately resolves to. The relations that step into an
// interconnect's subobjects - vpiElement (an array element or a net's array
// element) and vpiMember (a net's struct member) - are named for the relation,
// not for the kind of object reached, so the Iterate dispatcher recognizes them
// specially below.
// ===========================================================================

bool VpiIsInterconnectSubelementType(int type) {
  // §37.24 details 1 and 2: stepping into an interconnect reaches another
  // interconnect object - a nested interconnect array (a further dimension
  // level) or a leaf interconnect net.
  return type == vpiInterconnectArray || type == vpiInterconnectNet;
}

bool VpiIsInterconnectArrayDataTypespec(int typespec_type) {
  // §37.24 detail 1: vpiElement reaches an interconnect net's elements only
  // when the data type of the typespec it connects to is a packed or unpacked
  // array.
  return typespec_type == vpiArrayTypespec ||
         typespec_type == vpiPackedArrayTypespec;
}

bool VpiIsInterconnectStructDataTypespec(int typespec_type) {
  // §37.24 detail 1: vpiMember reaches an interconnect net's members only when
  // the data type of the typespec it connects to is a packed or unpacked
  // struct; a union is likewise member-bearing and reached the same way.
  return typespec_type == vpiStructTypespec ||
         typespec_type == vpiUnionTypespec;
}

int VpiInterconnectNetTypespecType(VpiHandle interconnect_net) {
  // §37.24 detail 1: an interconnect net's typespec is the typespec of the net
  // or nets it connects to (§37.16 detail 13 hands it back). Its data-type kind
  // selects whether vpiElement or vpiMember reaches the net's subobjects, so
  // report the kind of the net's typespec child; zero when it has none.
  if (!interconnect_net) return 0;
  for (auto* child : interconnect_net->children) {
    if (VpiIsTypespecType(child->type)) return child->type;
  }
  return 0;
}

// ===========================================================================
// §37.11 Instance arrays.
// ===========================================================================

bool VpiIsPrimitiveArrayType(int type) {
  // §37.11 (primitive-array diagram): a primitive array and the three concrete
  // forms drawn beneath it - gate, switch, and udp arrays.
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

bool VpiIsInstanceArrayType(int type) {
  // §37.11 (instance-array diagram): the module, interface, and program arrays
  // drawn beneath instance array, plus every primitive array (a primitive array
  // is itself a kind of instance array) and the instance-array supertype.
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
  // §37.11 detail 1: the expr reached from an instance array is the operation
  // object listing the array's actual connections, modeled as the array's first
  // operation child. A null, non-instance-array, or childless handle has none.
  if (!instance_array) return nullptr;
  if (!VpiIsInstanceArrayType(instance_array->type)) return nullptr;
  for (auto* child : instance_array->children) {
    if (child->type == vpiOperation) return child;
  }
  return nullptr;
}

bool VpiInstanceArrayConnectionsIsListOp(VpiHandle expr) {
  // §37.11 detail 1: that expr shall be a vpiOperation whose vpiOpType is
  // vpiListOp.
  return expr && expr->type == vpiOperation && expr->op_type == vpiListOp;
}

std::vector<VpiRangeDesc> VpiInstanceArrayRanges(
    const std::vector<VpiArrayDimension>& dims) {
  // §37.11 detail 2: one range per declared dimension, beginning with the
  // leftmost range of the array declaration and iterating through the
  // rightmost. Each dimension routes through §37.22's empty-range rule.
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

// §37.11 detail 2: the §37.22 range for an instance array's leftmost dimension,
// the one vpiLeftRange/vpiRightRange report. An array with no dimensions yields
// an empty range, so both relations report NULL.
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
  // §37.11 detail 2: vpiLeftRange returns the bound of the leftmost dimension;
  // defer to §37.22's vpiLeftRange.
  return VpiRangeLeftRange(LeftmostInstanceArrayRange(dims));
}

VpiHandle VpiInstanceArrayRightRange(
    const std::vector<VpiArrayDimension>& dims) {
  // §37.11 detail 2: the mirror of VpiInstanceArrayLeftRange.
  return VpiRangeRightRange(LeftmostInstanceArrayRange(dims));
}

}  // namespace delta
