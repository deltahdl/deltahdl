#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/vpi_constants.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"

namespace delta {

// ===========================================================================
// §37.28 Parameter, spec param, def param, param assign. The VPI object model
// for parameters (vpiParameter), type parameters (vpiTypeParameter), def params
// (vpiDefParam), and param assigns (vpiParamAssign). Most of the figure - the
// vpiName/vpiFullName/vpiSize/vpiConstType/vpiSigned properties, and the value
// served by vpi_get_value() (detail 1, provided by §38.34) - is carried by the
// generic machinery once the object's fields and children are populated. The
// helpers below carry the four relation rules the clause refines (details 2-5)
// and drive the public vpi_handle dispatch.
// ===========================================================================

// §37.28 detail 2: vpiTypespec of a type parameter - the typespec it resolved
// to at the end of elaboration, handed back without following any typedef alias
// to its underlying type (deliberately not applying §37.25/§37.30's alias
// resolution). NULL when the type parameter carries no such typespec.
VpiHandle VpiTypeParameterTypespec(VpiHandle type_parameter);

// §37.28 detail 3: vpiExpr of a parameter - its default. For a value parameter
// this is the default value expression; for a type parameter it is the default
// typespec. NULL when no default is recorded.
VpiHandle VpiParameterDefaultExpr(VpiHandle parameter);

// §37.28 detail 4: vpiLhs of a param assign - the value or type parameter the
// assignment overrides, i.e. the parameter-kind object among its children. NULL
// when the param assign overrides nothing of that kind.
VpiHandle VpiParamAssignLhs(VpiHandle param_assign);

// §37.28 detail 5: vpiLeftRange / vpiRightRange of a value parameter. A
// parameter declared without an explicit range reports a null handle for both;
// otherwise each reaches the corresponding range-bound expression.
VpiHandle VpiParameterLeftRange(VpiHandle parameter);
VpiHandle VpiParameterRightRange(VpiHandle parameter);

// ===========================================================================
// §37.29 Virtual interface. The VPI object model for a virtual interface var
// (vpiVirtualInterfaceVar): a class/scope variable that holds an interface
// instance. The figure's properties (vpiName/vpiFullName/vpiIsModPort) and its
// vpiTypespec reach to an interface typespec (§37.30) are served by the generic
// Get/GetStr/Handle machinery once the var's fields and children are populated.
// The two relations the clause refines - vpiExpr (the declaration-time
// assignment, detail 1) and vpiActual (the currently held instance, Example 2)
// - are carried by the helpers below, which also drive the public vpi_handle
// dispatch. Detail 2 constrains which objects may serve as a virtual interface
// var's interface expr.
// ===========================================================================

// §37.29 (figure, "interface expr" group): the object kinds that may sit at the
// far end of a virtual interface var's vpiExpr - an interface, a modport,
// another virtual interface var, a ref obj, or a constant.
bool VpiIsInterfaceExprType(int type);

// §37.29 detail 2: whether an object of an interface-expr kind is a legal
// interface expr. A ref obj qualifies only when its vpiActual is an interface
// or a modport (a local declaration passed through a port); a constant only
// when its vpiConstType is vpiNullConst; an interface, modport, or virtual
// interface var always qualifies.
bool VpiInterfaceExprIsValid(VpiHandle expr);

// §37.29 detail 1: vpiExpr of a virtual interface var - the interface instance
// assigned to it in its declaration, or NULL when none was assigned (and when
// the only candidate fails the detail-2 constraint).
VpiHandle VpiVirtualInterfaceExpr(VpiHandle var);

// ===========================================================================
// §37.30 Interface typespec. An interface typespec (vpiInterfaceTypespec) is a
// typespec (§37.25) denoting a virtual interface or one of its modports. Its
// vpiName (the typedef's name) and its vpiParamAssign relation are served by
// the generic GetStr/Iterate machinery once the name and param-assign children
// are populated; the two numbered "Details" that refine the model - vpiDefName
// (detail 1) and vpiParent (detail 2) - are carried by the helpers below, which
// also drive the public vpi_get_str/vpi_handle dispatch.
// ===========================================================================

// §37.30 detail 1: vpiDefName of an interface typespec. When the typespec
// represents a modport the definition name is the modport identifier; when it
// represents an interface it is the interface declaration's identifier. Either
// definition name is stored on the typespec, so it is reported directly. NULL
// for a handle that is not an interface typespec or that carries no definition
// name.
const char* VpiInterfaceTypespecDefName(VpiHandle interface_typespec);

// §37.30 detail 2: vpiParent of an interface typespec. A typespec that
// represents a modport reaches the interface typespec of the interface it
// belongs to; a typespec that represents an interface has no parent (NULL).
VpiHandle VpiInterfaceTypespecParent(VpiHandle interface_typespec);

// ===========================================================================
// §37.48 Clocking block. The VPI object model for a clocking block
// (vpiClockingBlock) and the clocking io decls (vpiClockingIODecl) it contains.
// Most of the figure - the input/output skew delay controls, the clocking
// event, the contained io/property/sequence decls, and the vpiName/vpiFullName
// and vpiInputEdge/vpiOutputEdge properties - is served by the generic
// Get/GetStr/ Iterate/Handle machinery once the objects' fields and children
// are populated; detail 1 only records that those skew/edge relations target
// the default constructs on a clocking block and the io decl itself on an io
// decl. The three numbered Details that refine traversal - vpiPrefix (detail
// 2), vpiActual (detail 3), and vpiExpr of an io decl (detail 4) - are carried
// by the helpers below, which also drive the public vpi_handle dispatch.
// ===========================================================================

// §37.48 detail 2: vpiPrefix of a clocking block - the virtual interface var
// the clocking block expression is immediately prefixed by (e.g., "vif.cb"). It
// is modeled as a virtual interface var child; a clocking block that is not so
// prefixed has none and reports NULL.
VpiHandle VpiClockingBlockPrefix(VpiHandle block);

// §37.48 detail 3: vpiActual of a clocking block - the concrete clocking block
// selected through its virtual interface prefix. When the prefix is a virtual
// interface that holds no value at the current simulation time (its own
// vpiActual is NULL), the clocking block's vpiActual is NULL as well.
VpiHandle VpiClockingBlockActual(VpiHandle block);

// §37.48 (figure, clocking io decl -> nets / variables / ref obj): the object
// kinds a clocking io decl's vpiExpr relation may reach - the net, variable, or
// ref obj the io decl names.
bool VpiIsClockingIODeclExprType(int type);

// §37.48 detail 4: vpiExpr of a clocking io decl - the expression or ref obj
// the io decl names. For "enable = top.mem1.enable" the io decl "enable"
// reaches a handle to the ref obj "top.mem1.enable"; NULL when the io decl
// names nothing.
VpiHandle VpiClockingIODeclExpr(VpiHandle io_decl);

// ===========================================================================
// §37.13 IO declaration. The VPI object model for an io decl (vpiIODecl): a
// module/UDP/task/function port or argument declaration. The diagram's
// properties (vpiDirection/vpiName/vpiScalar/vpiSigned/vpiSize/vpiVector) and
// the structural reach from instance/UDP/task-func/module are served by the
// generic Get/Handle machinery; the four numbered details that refine the
// model are carried by the helpers below. The range relations (detail 4) are
// defined to equal the corresponding typespec's, so they rest on §37.25.
// ===========================================================================

// §37.13 (vpiExpr targets): the object kinds the single vpiExpr relation of an
// io decl may draw to - a ref obj, an interface tf decl, a connected net or
// variable, or (for a virtual interface) a virtual interface var.
bool VpiIsIoDeclExprType(int type);

// §37.13 detail 2: the kind of handle vpiExpr of an io decl yields. An io decl
// passed by reference, or one that is itself an interface or a modport, hands
// back a ref obj (vpiRefObj). A virtual-interface io decl hands back a virtual
// interface var (vpiVirtualInterfaceVar). Any other io decl reaches its
// connected expression - the net, variable, or interface tf decl supplied as
// default_expr_type - directly.
int VpiIoDeclExprType(bool passed_by_reference, bool is_interface_or_modport,
                      bool is_virtual_interface, int default_expr_type);

// §37.13 details 1 and 3: the vpiDirection an io decl reports. Detail 3 takes
// precedence: an io decl whose vpiExpr is a ref obj whose vpiActual is an
// interface or modport declaration, or whose vpiExpr is a virtual interface
// var, has an undefined direction (reported as vpiNoDirection). Otherwise
// detail 1 applies - a port or argument passed by reference reports vpiRef, and
// every other passing mode keeps its declared direction.
int VpiIoDeclDirection(int declared_direction, bool passed_by_reference,
                       bool expr_is_ref_obj_to_interface_or_modport,
                       bool expr_is_virtual_interface_var);

// §37.13 detail 2: the io decl's vpiExpr target - the designated connection
// child reached through the single vpiExpr relation. That child's own type is
// one of the expr-target kinds (not vpiExpr), so the shared traversal cannot
// find it by type; this returns the first such child. Null when the handle is
// null, is not an io decl, or carries no expr-target child.
VpiHandle VpiIoDeclExpr(VpiHandle io_decl);

// §37.13 detail 4 (woven with §37.25): the ranges vpi_iterate(vpiRange,
// io_decl) returns are the same as for the io decl's corresponding typespec, so
// this defers to §37.25's typespec range helper.
std::vector<VpiRangeDesc> VpiIoDeclRanges(
    const std::vector<VpiArrayDimension>& dims);

// §37.13 detail 4 (woven with §37.25): vpiLeftRange of an io decl, identical to
// the corresponding typespec's vpiLeftRange.
VpiHandle VpiIoDeclLeftRange(const std::vector<VpiArrayDimension>& dims);

// §37.13 detail 4 (woven with §37.25): vpiRightRange of an io decl, the mirror
// of VpiIoDeclLeftRange.
VpiHandle VpiIoDeclRightRange(const std::vector<VpiArrayDimension>& dims);

// ===========================================================================
// §37.14 Ports and §37.15 Reference objects. The two clauses share a model: a
// port's vpiHighConn/vpiLowConn connections are reached the same way a ref
// obj's are, and the lowConn of an interface port is itself a ref obj (§37.14
// detail 5), so the connection helpers below serve both. The numbered "Details"
// that carry decision rules are realized as helpers; the diagram's structural
// relations are served by the generic Handle/Get machinery once the designated
// connection pointers are populated.
// ===========================================================================

// §37.14 detail 1: the three port types a port may report through
// vpi_get(vpiPortType). The value is determined by the formal, never the
// actual.
bool VpiIsValidPortType(int port_type);

// §37.14 detail 1: the port type derived from what the formal denotes - an
// interface formal yields vpiInterfacePort, a modport formal vpiModportPort,
// and any ordinary formal vpiPort. The actual a port connects to never changes
// this.
int VpiPortTypeFromFormal(bool formal_is_interface, bool formal_is_modport);

// §37.14 detail 2: vpi_get_delays() and vpi_put_delays() are not applicable to
// an interface port. FALSE for an interface port; TRUE for any other port type.
bool VpiPortDelaysApplicable(int port_type);

// §37.14 details 3, 4, and 10 (shared with §37.15): the hierarchically higher
// (closer to the top module) port connection. NULL when the instance has no
// connection to the port. Also serves a ref obj's vpiHighConn.
VpiHandle VpiHighConn(VpiHandle obj);

// §37.14 details 3, 4, and 10 (shared with §37.15): the lower (further from the
// top module) port connection. NULL for a null port. Also serves a ref obj's
// vpiLowConn.
VpiHandle VpiLowConn(VpiHandle obj);

// §37.14 detail 5: the lowConn of a vpiInterfacePort shall always be a ref obj.
// TRUE when the port is not an interface port, or it is and its lowConn is a
// ref obj; FALSE when an interface port's lowConn is missing or some other
// kind.
bool VpiPortLowConnSatisfiesInterfaceRule(VpiHandle port);

// §37.14 detail 6: vpiScalar is TRUE when the port is exactly one bit wide. The
// width is the port's own, never anything about what is connected to it.
bool VpiPortScalar(int port_width);

// §37.14 detail 6: vpiVector is TRUE when the port is more than one bit wide.
bool VpiPortVector(int port_width);

// §37.14 detail 7: vpiPortIndex and vpiName do not apply to a port bit (only to
// a whole port). TRUE for a port, FALSE for a port bit.
bool VpiPortIndexAndNameApply(int type);

// §37.14 detail 8: the name vpi_get_str(vpiName) returns for a port. An
// explicitly named port returns its explicit name; otherwise, if an inferred
// name exists, that name is returned; otherwise NULL. An empty C string counts
// as "no name".
const char* VpiPortName(bool explicitly_named, std::string_view explicit_name,
                        std::string_view inferred_name);

// §37.14 detail 11: vpiSize for a port. A null port reports 0; any other port
// reports its bit width.
int VpiPortSize(bool is_null_port, int port_width);

// §37.15 detail 5: vpiGeneric for a ref obj. TRUE when the ref obj refers to a
// generic interface, FALSE when it refers to a non-generic interface, and
// vpiUndefined for every other kind of ref obj.
int VpiRefObjGeneric(bool refers_to_interface, bool is_generic_interface);

// §37.15 detail 6: vpiDefName for a ref obj whose vpiActual is an interface or
// a modport returns that interface's definition name or the modport name. NULL
// for a ref obj whose actual is neither (or which is unbound).
const char* VpiRefObjDefName(VpiHandle ref_obj);

// §37.15 detail 7: the vpiTypespec relation returns NULL for a ref obj whose
// vpiActual is not a net, variable, or part select; otherwise it returns the
// ref obj's typespec child.
VpiHandle VpiRefObjTypespec(VpiHandle ref_obj);

// ===========================================================================
// §37.16 Nets. The VPI net object model, the net counterpart of §37.17's
// variable model. Each helper applies one of the clause's numbered "Details" so
// the rule can be observed independently of the surrounding elaboration and
// driver-update machinery. Range relations (details 1 and 26) are woven onto
// §37.22's range helpers, and the prefix and member-name rules (details 31 and
// 34) reuse §37.17's prefix/name structures, since a net prefix and a variable
// prefix carry the same shape.
// ===========================================================================

// §37.16 detail 1: a net declared as an array with one or more unpacked ranges
// is an array net.
bool VpiIsArrayNet(int unpacked_range_count);

// §37.16 detail 1: a packed struct net, packed union net, or enum net declared
// with one or more explicit packed ranges is a packed array net. The net_type
// is the declared net object kind; explicit_packed_range_count counts only the
// ranges written on the declaration, never the implicit element ranges.
bool VpiIsPackedArrayNet(int net_type, int explicit_packed_range_count);

// §37.16 detail 2: vpiArrayMember is TRUE exactly when a net is an element of
// an array net, read from the net's vpiParent prefix. (The older vpiArray
// property is deprecated for the same role.)
bool VpiNetIsArrayMember(VpiHandle net);

// §37.16 detail 2: vpiPackedArrayMember is TRUE for a packed struct net, packed
// union net, enum net, or packed array net that is an element of a packed array
// net (its vpiParent prefix is a packed array net).
bool VpiNetIsPackedArrayMember(VpiHandle net);

// §37.16 detail 3: a net bit of a logic net or bit net is always reachable
// through vpiBit, regardless of whether the vector was expanded. True for a
// logic net or a bit net.
bool VpiNetBitIteratorApplies(int net_type);

// §37.16 detail 5: continuous assignments and primitive terminals
// (vpiContAssign and vpiPrimTerm) shall only be accessed from a scalar net or a
// bit-select.
bool VpiNetTerminalAccessAllowed(bool is_scalar_net_or_bit_select);

// §37.16 details 6 and 7: the granularity a vpiPorts or vpiPortInst iteration
// hands back for a given reference handle - either the individual port bits (or
// scalar ports) matching the reference, or a handle to the entire port.
enum class VpiPortGranularity : std::uint8_t {
  kPortBits,    // the port bits / scalar ports the reference selects
  kEntirePort,  // a handle to the whole port
};

// §37.16 detail 6: the granularity vpiPorts returns. A net bit reference yields
// the matching port bits; an entire net or array net reference yields a handle
// to the entire port.
VpiPortGranularity VpiPortsReferenceGranularity(int ref_type);

// §37.16 detail 7: the granularity vpiPortInst returns. A bit or scalar
// reference yields port bits or scalar ports, unless the port's highconn is a
// complex expression whose bit index cannot be determined, in which case the
// entire port is returned. An entire net or array net reference always yields
// the entire port.
VpiPortGranularity VpiPortInstReferenceGranularity(
    bool ref_is_bit_or_scalar, bool ref_is_entire_net_or_array,
    bool highconn_bit_index_undeterminable);

// §37.16 detail 8: a vpiPortInst reference that lies within the highconn
// expression but is connected to none of the port's bits (which can happen on a
// size mismatch) does not qualify as a member of that iteration.
bool VpiPortInstReferenceQualifies(bool connected_to_any_port_bit);

// §37.16 detail 9: vpiLineNo of a net. An implicit net reports 0; an explicitly
// declared net reports the line it was declared on.
int VpiNetLineNo(bool implicit, int declared_line);

// §37.3.3: whether an object kind carries the source-location properties
// vpiLineNo and vpiFile. True for every object that corresponds to something in
// the source text; false for the kinds §37.3.3 names as exceptions - those that
// have no single source line or file (callbacks, delay terms and devices,
// intermodule paths, iterators, the time queue, and generate-scope arrays and
// scopes).
bool VpiHasLocationProperties(int type);

// §37.16 detail 10: vpi_handle(vpiIndex, net_bit) returns the bit index of a
// net bit - its single innermost index.
VpiHandle VpiNetBitIndex(const std::vector<VpiHandle>& indices_inner_to_outer);

// §37.16 detail 10: vpi_iterate(vpiIndex, net_bit) over a multidimensional net
// array bit-select returns the indices starting with the net bit's index and
// working outward; the inputs are already in that order.
std::vector<VpiHandle> VpiNetBitIndicesOutward(
    const std::vector<VpiHandle>& indices_inner_to_outer);

// §37.16 detail 11: vpiNetType for a user-defined nettype. A net not declared
// with a nettype reports vpiNettypeNet; any part (a select) of a net declared
// with a nettype reports vpiNettypeNetSelect.
int VpiNetNettypeValue(bool is_part_of_nettype_net);

// §37.16 detail 11: vpiDriver and vpiLocalDriver iterations are not supported
// for a net whose vpiNetType is vpiNettypeNetSelect.
bool VpiNetDriverIterationSupported(int nettype_value);

// §37.16 detail 12: vpiNetType for an interconnect net or interconnect net
// select is vpiInterconnect.
int VpiInterconnectNetType();

// §37.16 detail 12: vpiResolvedNetType for an interconnect net that is a
// simulated net (see 23.3.3.7) is the resolved type of that simulated net.
int VpiInterconnectResolvedNetType(int simulated_resolved_type);

// §37.16 detail 13: vpiTypespec returns NULL for an interconnect array; for any
// other net it is the net's typespec child.
VpiHandle VpiNetTypespec(VpiHandle net);

// §37.16 detail 21: vpiExpanded queried on a net bit reports the value of the
// property for the bit's parent net.
bool VpiNetBitExpanded(VpiHandle net_bit);

// §37.16 detail 23: vpiConstantSelect for a net or net bit. TRUE when the
// object has no parent (vpiParent returns NULL), or when every index expression
// in the select is an elaboration-time constant and every selected element
// denotes a struct/union net member or a packed/unpacked array element with
// static bounds (see A.8.4); FALSE otherwise.
bool VpiNetConstantSelect(bool has_parent, bool all_indices_constant,
                          bool all_elements_static_members);

// §37.16 detail 24: the inputs vpiSize reads for a net object.
struct VpiNetSizeQuery {
  int net_type = 0;
  bool packed = false;               // struct/union net: packed vs unpacked
  int bit_width = 0;                 // integral-typed net: size in bits
  int array_element_count = 0;       // array net: number of nets in the array
  int interconnect_array_count = 0;  // interconnect array: number of elements
  int connected_net_size = 0;        // interconnect net (not array): connected
                                     // net's vpiSize
  int member_count = 0;              // unpacked struct/union net: member count
};

// §37.16 detail 24: vpiSize for a net object. An interconnect array reports its
// element count; an interconnect net that is not an array reports the size of
// the net it connects to; an array net reports the number of nets in the array;
// a net of integral data type (see 6.11.1) reports its size in bits; a net bit
// reports 1; an unpacked struct or union net reports its member count. Every
// other net's vpiSize is undefined and reported as 0.
int VpiNetSize(const VpiNetSizeQuery& query);

// §37.16 detail 25: vpi_iterate(vpiIndex, net) over a net within an array net
// returns the selecting indices starting with the net's index and working
// outward. A net that is not an element of an array net (vpiArrayMember FALSE)
// has no index iteration, signalled by an empty result.
std::vector<VpiHandle> VpiNetIndicesOutward(
    bool is_array_member, const std::vector<VpiHandle>& indices_inner_to_outer);

// §37.16 detail 26 (woven with §37.22): the ranges vpi_iterate(vpiRange, net)
// returns, one per dimension. For an array net the iteration runs from the
// leftmost unpacked range to the rightmost; for a packed array, logic, or bit
// net it runs from the leftmost packed range to the rightmost. Implicit element
// ranges are dropped (detail 1).
std::vector<VpiRangeDesc> VpiNetRanges(
    const std::vector<VpiArrayDimension>& dims);

// §37.16 detail 26: vpiLeftRange of a bit, logic, or packed array net - the
// bound of the leftmost packed dimension. NULL when the net has no dimensions
// or that leftmost range is empty.
VpiHandle VpiNetLeftRange(const std::vector<VpiArrayDimension>& dims);

// §37.16 detail 26: vpiRightRange of a net, the mirror of VpiNetLeftRange.
VpiHandle VpiNetRightRange(const std::vector<VpiArrayDimension>& dims);

// §37.16 detail 28: the inputs the scalar/vector rules read for a net.
struct VpiNetScalarVectorQuery {
  int net_type = 0;
  bool has_packed_dimension = false;  // bit/logic net: any packed dimensions
  bool packed = false;                // struct/union net: packed vs unpacked
  bool base_is_scalar = false;        // enum net: base typespec's vpiScalar
  bool base_is_vector = false;        // enum net: base typespec's vpiVector
  bool element_is_scalar = false;     // array net: an element's vpiScalar
  bool element_is_vector = false;     // array net: an element's vpiVector
};

// §37.16 detail 28: vpiScalar for a net. A bit or logic net with no packed
// dimension and a net bit are scalars; an enum net defers to its base typespec;
// an array net defers to an element; every other net object is not a scalar.
bool VpiNetScalar(const VpiNetScalarVectorQuery& query);

// §37.16 detail 28: vpiVector for a net. A bit or logic net with a packed
// dimension and the other integral-typed nets (integer, time, byte, shortint,
// int, longint, packed struct/union, packed array net) are vectors; an enum net
// defers to its base typespec; an array net defers to an element; every other
// net object is not a vector.
bool VpiNetVector(const VpiNetScalarVectorQuery& query);

// §37.16 detail 30: whether a net kind has a value property. Array nets,
// unpacked struct nets, unpacked union nets, and interconnect arrays do not;
// every other net does.
bool VpiNetHasValueProperty(int net_type, bool packed_struct_union);

// §37.16 detail 31: vpiParent of a net. Scanning the prefix objects rightmost
// to leftmost (the order given), the first qualifying prefix is returned - a
// struct/union net, a struct/union member net, or the largest containing packed
// or unpacked array net; NULL when none qualifies. Reuses §37.17's prefix
// descriptor, whose shape is shared between the two object models.
VpiHandle VpiNetParent(const std::vector<VpiParentPrefix>& prefixes);

// §37.16 detail 32: vpiElement iterates the subelements of a packed array net,
// one dimension at a time. True for a packed array net, false for any other
// net.
bool VpiNetElementIteratorApplies(int net_type);

// §37.16 detail 32: the subelements a vpiElement iteration over a packed array
// net returns - its element children, in declaration order.
std::vector<VpiHandle> VpiPackedArrayNetElements(VpiHandle packed_array_net);

// §37.16 detail 33: vpiStructUnionMember is TRUE for a net or array net that is
// a direct member of a struct net or union net (its vpiParent is a struct/union
// net), FALSE for any other net, and is not defined for a net bit (reported
// FALSE).
bool VpiNetStructUnionMember(VpiHandle net);

// §37.16 detail 34: vpiName of a net - the leaf member with its own index/slice
// but none of its struct/union-net prefixes. Reuses §37.17's name-parts shape.
std::string VpiNetName(const VpiVariableNameParts& parts);

// §37.16 detail 34: vpiDecompile of a net - the struct/union-net prefixes
// joined to the member (and its index/slice) without the top-level scope, so it
// resolves for any non-top-level scope context.
std::string VpiNetDecompile(const VpiVariableNameParts& parts);

// §37.16 detail 34: vpiFullName of a net - the top-level scope prefixed to the
// decompile form.
std::string VpiNetFullName(const VpiVariableNameParts& parts);

// ===========================================================================
// §37.24 Generic interconnect.
// ===========================================================================

// §37.24 details 1 and 2: the subobjects reached when stepping into an
// interconnect (an array's elements, a net's array elements, or a net's struct
// members) are themselves interconnect objects - a nested interconnect array or
// a leaf interconnect net.
bool VpiIsInterconnectSubelementType(int type);

// §37.24 detail 1: an interconnect net supports vpiElement only when the data
// type of the typespec it connects to is a packed or unpacked array.
bool VpiIsInterconnectArrayDataTypespec(int typespec_type);

// §37.24 detail 1: an interconnect net supports vpiMember only when the data
// type of the typespec it connects to is a packed or unpacked struct (a union
// is reached the same way).
bool VpiIsInterconnectStructDataTypespec(int typespec_type);

// §37.24 detail 1: the data-type kind of the typespec an interconnect net
// connects to, used to decide whether vpiElement or vpiMember reaches the net's
// subobjects. Zero when the net carries no typespec.
int VpiInterconnectNetTypespecType(VpiHandle interconnect_net);

// ===========================================================================
// §37.11 Instance arrays.
// ===========================================================================

// §37.11 (primitive-array diagram): the primitive-array group - a primitive
// array and the concrete gate, switch, and udp array forms drawn beneath it.
bool VpiIsPrimitiveArrayType(int type);

// §37.11 (instance-array diagram): the instance-array group - the module,
// interface, and program arrays drawn beneath instance array, plus every
// primitive array (a primitive array is itself a kind of instance array) and
// the instance-array supertype. The details below apply to this whole group.
bool VpiIsInstanceArrayType(int type);

// §37.11 detail 1: traversing from an instance array to its expr returns the
// operation object that gives access to the actual list of connections to the
// array. Modeled as the array's first operation child; null when the handle is
// null, is not an instance array, or carries no such child.
VpiHandle VpiInstanceArrayConnections(VpiHandle instance_array);

// §37.11 detail 1: the expr an instance array traverses to shall be a simple
// expression object of type vpiOperation whose vpiOpType is vpiListOp.
bool VpiInstanceArrayConnectionsIsListOp(VpiHandle expr);

// §37.11 detail 2: the ranges vpi_iterate(vpiRange, instance_array) returns,
// one per declared dimension, beginning with the leftmost range of the
// declaration and running through the rightmost. Each dimension routes through
// §37.22's empty-range rule.
std::vector<VpiRangeDesc> VpiInstanceArrayRanges(
    const std::vector<VpiArrayDimension>& dims);

// §37.11 detail 2: vpiLeftRange of an instance array - the left bound of the
// leftmost dimension of a (possibly multidimensional) array. NULL when the
// array has no dimensions or that leftmost range is empty (§37.22).
VpiHandle VpiInstanceArrayLeftRange(const std::vector<VpiArrayDimension>& dims);

// §37.11 detail 2: vpiRightRange of an instance array, the mirror of
// VpiInstanceArrayLeftRange.
VpiHandle VpiInstanceArrayRightRange(
    const std::vector<VpiArrayDimension>& dims);
}  // namespace delta
