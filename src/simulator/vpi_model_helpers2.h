#pragma once

#include <string>
#include <string_view>
#include <vector>

#include "simulator/vpi_constants.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"

namespace delta {

// ===========================================================================
// §37.43 Frames. The VPI object model for a frame - a dynamically activated
// procedural scope together with its locally declared automatic variables,
// events, and event arrays, if any (detail 1). A frame carries one Boolean
// property (vpiActive, applied by VpiContext::Get - the same property a thread
// reports, §37.44) and the relations modeled by the helpers below. A frame is
// woven to its thread by the frame--thread edge shared with §37.44: §37.44's
// VpiThreadFrame walks that edge from the thread to its active frame, and
// VpiFrameThread (below) walks it back. Frame specific callbacks are §38.36.1's
// (detail 8). The frame object model is not backwards compatible with
// IEEE Std 1800-2017 or earlier (detail 7).
// ===========================================================================

// §37.43 (vpiOrigin targets / detail 6): the object kinds a frame's vpiOrigin
// can reach - the point in the elaboration hierarchy from which the frame was
// activated. The diagram draws these as a scope, a (system/method) task or
// function call, or a net or net array. The net and net-array cases cover a
// frame activated for a nettype's user-defined resolution function.
bool VpiIsFrameOriginType(int type);

// §37.43 (vpiParent -> frame / detail 5): the frame from which this child frame
// was activated, reached up the parent chain when that parent is itself a
// frame. Null for a null handle, a root frame with no parent, or a non-frame
// parent.
VpiHandle VpiFrameParent(VpiHandle frame);

// §37.43 (vpiOrigin / detail 6): the elaboration-hierarchy point a frame was
// activated from, modeled as the frame's first origin-kind child (see
// VpiIsFrameOriginType). Null for a null handle or a frame with no origin.
VpiHandle VpiFrameOrigin(VpiHandle frame);

// §37.43 (frame to stmt transition / details 4 and 5): the statement reached
// from a frame. For the active frame this is the currently active statement
// within it; for a parent frame it is the atomic statement or scope whose
// execution activated the child frame. Modeled as the frame's first statement
// child. Null for a null handle or a frame with no statement attached.
VpiHandle VpiFrameStmt(VpiHandle frame);

// §37.43 (frame--thread edge): the thread a frame belongs to. This is the
// reverse of §37.44's VpiThreadFrame, which reaches the active frame from the
// thread; here the frame reaches its thread, modeled as its first thread child.
// Null for a null handle or a frame with no thread attached.
VpiHandle VpiFrameThread(VpiHandle frame);

// §37.43 (vpiAutomatics / detail 1): the automatic objects a frame locally
// declares - its automatic variables, named events, and named event arrays, in
// order. A null handle yields none.
std::vector<VpiHandle> VpiFrameAutomatics(VpiHandle frame);

// ===========================================================================
// §37.44 Threads. The VPI object model for a thread - a SystemVerilog process
// such as an always procedure or a branch of a fork construct (detail 1). The
// diagram gives a thread one Boolean property (vpiActive, applied by
// VpiContext::Get) and four relations modeled by the helpers below. Thread
// specific callbacks are §38.36.1's (detail 2).
// ===========================================================================

// §37.44 (vpiParent -> thread): the thread that spawned this one, reached up
// the parent chain. Returns the thread's parent when that parent is itself a
// thread; null for a null handle, a root thread with no parent, or a parent
// that is not a thread.
VpiHandle VpiThreadParent(VpiHandle thread);

// §37.44 (vpiOrigin -> stmt): the statement a thread originated from, modeled
// as the thread's first statement child. Null for a null handle or a thread
// with no origin statement attached.
VpiHandle VpiThreadOrigin(VpiHandle thread);

// §37.44 (frame -- thread / detail 1): the active frame of a thread. As a
// thread descends a call chain of tasks and functions a new frame is activated
// for each one entered, and at most one is active at a time (§37.43); this
// returns that frame, modeled as the thread's first frame child. Null for a
// null handle or a thread with no frame attached.
VpiHandle VpiThreadFrame(VpiHandle thread);

// §37.44 (thread one-to-many thread): the threads spawned by this thread, as
// the iteration over its thread children yields them, in order. A null handle
// yields none.
std::vector<VpiHandle> VpiThreadThreads(VpiHandle thread);

// ===========================================================================
// §37.22 Object range. A range object carries the bounds of one array
// dimension. §37.17's range relations (details 4 and 6) are woven onto these
// helpers, so a range that one subclause calls "empty" behaves identically in
// the other.
// ===========================================================================

// §37.22 detail 1: a range object's contents. An empty range has no elements;
// it stands in for an associative-array dimension, an empty dynamic array or
// queue, and any range obtained from a typespec for a dynamic-array, queue, or
// associative dimension. A non-empty range carries the bound expressions
// reached through vpiLeftRange/vpiRightRange and an element count.
struct VpiRangeDesc {
  bool empty = false;
  VpiHandle left_expr = nullptr;
  VpiHandle right_expr = nullptr;
  int size = 0;
};

// §37.22 detail 1 (and §37.17 detail 4): the array-dimension kinds a range can
// describe, and which of them are represented by an empty range. Fixed packed
// and unpacked dimensions have real bounds; dynamic-array, queue, and
// associative dimensions are empty ranges.
enum class VpiDimensionKind {
  kPacked,
  kFixedUnpacked,
  kDynamic,
  kQueue,
  kAssoc,
};

// §37.22 detail 1: whether a dimension of the given kind is an empty range.
bool VpiDimensionRangeIsEmpty(VpiDimensionKind kind);

// §37.22 detail 2: vpiSize of a range - 0 for an empty range, otherwise the
// range's element count.
int VpiRangeSize(const VpiRangeDesc& range);

// §37.22 detail 2: vpiLeftRange of a range - NULL for an empty range, otherwise
// the left bound expression. §37.17 detail 6 reuses this for a variable's
// leftmost dimension.
VpiHandle VpiRangeLeftRange(const VpiRangeDesc& range);

// §37.22 detail 2: vpiRightRange of a range, the mirror of VpiRangeLeftRange.
VpiHandle VpiRangeRightRange(const VpiRangeDesc& range);

// ===========================================================================
// §37.17 Variables.
// ===========================================================================

// §37.17 detail 19: a logic var is the same object kind as a reg; treat either
// as a logic variable so an existing reg-typed object is classified correctly.
bool VpiIsLogicVarType(int type);

// §37.17 detail 19: an array var is the same object kind as a reg array; accept
// either kind wherever an array variable is meant.
bool VpiIsArrayVarType(int type);

// §37.17 detail 1: a variable declared as an array with one or more unpacked
// ranges is an array var.
bool VpiIsArrayVar(int unpacked_range_count);

// §37.17 detail 2: vpiArrayMember is TRUE exactly when a variable is an element
// of an array variable, read from the variable's vpiParent prefix.
bool VpiVariableIsArrayMember(VpiHandle var);

// §37.17 detail 17: vpiStructUnionMember is TRUE when a variable's vpiParent
// prefix is a struct or union variable.
bool VpiVariableIsStructUnionMember(VpiHandle var);

// §37.17 detail 8: a variable's initialization expression, reached through
// vpiExpr (modeled as the variable's first child). Null when the variable has
// no initialization expression.
VpiHandle VpiVariableInitExpr(VpiHandle var);

// §37.17 detail 14: whether the cbSizeChange callback is applicable to a
// variable. It applies only to dynamic arrays, associative arrays, queues, and
// string variables; array_type is the variable's vpiArrayType (0 when not an
// array). The detail's firing-order and new-size-value semantics need a
// size-change callback engine the simulator does not have, so only
// applicability is realized here.
bool VpiSizeChangeCallbackApplies(int array_type, bool is_string_var);

// §37.17 detail 4: one dimension of a variable as the vpiRange iteration sees
// it. The kind decides whether the dimension yields an empty range (§37.22); a
// fixed dimension also carries its bounds and size. An implicit element range
// (the implicit range of packed struct/union elements, or an enum var's base
// type) is excluded from a packed array's range iteration.
struct VpiArrayDimension {
  VpiDimensionKind kind = VpiDimensionKind::kFixedUnpacked;
  VpiHandle left_expr = nullptr;
  VpiHandle right_expr = nullptr;
  int size = 0;
  bool implicit_element_range = false;
};

// §37.17 detail 4: the ranges vpi_iterate(vpiRange, array_var) returns, one per
// dimension from leftmost to rightmost. A dynamic-array, queue, or associative
// dimension contributes an empty range (§37.22); a fixed dimension contributes
// its bounds. Implicit element ranges are dropped.
std::vector<VpiRangeDesc> VpiArrayVarRanges(
    const std::vector<VpiArrayDimension>& dims);

// §37.17 detail 6: vpiLeftRange of a variable - the left bound of its leftmost
// dimension (leftmost packed dimension for a packed array, leftmost unpacked
// dimension for an unpacked array). NULL when the variable has no members or
// that leftmost range is empty (§37.22).
VpiHandle VpiVariableLeftRange(const std::vector<VpiArrayDimension>& dims,
                               bool has_members);

// §37.17 detail 6: vpiRightRange of a variable, the mirror of
// VpiVariableLeftRange.
VpiHandle VpiVariableRightRange(const std::vector<VpiArrayDimension>& dims,
                                bool has_members);

// §37.17 detail 5: vpi_handle(vpiIndex, var_select) returns the index of a var
// select within a one-dimensional array - its single (innermost) index.
VpiHandle VpiSelectSingleIndex(
    const std::vector<VpiHandle>& indices_inner_to_outer);

// §37.17 details 5, 13, and 18: vpi_iterate(vpiIndex, ...) over a var select, a
// var bit, or an array-member variable returns the selecting index expressions
// starting with the innermost index and working outward; the inputs are already
// in that order.
std::vector<VpiHandle> VpiSelectIndicesOutward(
    const std::vector<VpiHandle>& indices_inner_to_outer);

// §37.17 details 9 and 10: the inputs vpiSize reads for a variable or var
// select.
struct VpiVariableSizeQuery {
  int var_type = 0;
  bool packed = false;  // struct/union var: packed vs unpacked
  int bit_width = 0;    // integer-typed/packed/enum var, packed var select
  int array_element_count = 0;  // variable array: number of element variables
  int string_length = 0;        // string var: current character count
  int field_count = 0;          // unpacked struct/union var: number of fields
};

// §37.17 details 9 and 10: vpiSize for a variable object. A variable array
// reports its element count; an integer-typed, packed struct/union, packed
// array, enum var, or packed var select reports its bit width; a string var
// reports its current character count; an unpacked struct/union reports its
// field count; a var bit reports 1. Every other variable's vpiSize is undefined
// and reported as 0.
int VpiVariableSize(const VpiVariableSizeQuery& query);

// §37.41 detail 12: vpiSize of a function. When the function's vpiReturn
// variable has a defined size that can be determined without evaluating the
// function, vpiSize for the function is the same as vpiSize for that variable.
// A void function reports 0. For every other case the behavior is undefined;
// this helper reports 0 there, the same not-defined sentinel VpiVariableSize
// uses.
int VpiFunctionSize(bool is_void_function, bool return_size_defined,
                    int return_var_size);

// §37.17 detail 11: whether a variable kind has a value property. Array, class,
// and virtual-interface variables do not; an unpacked struct or union variable
// (vpiVector FALSE) does not; every other variable kind does.
bool VpiVariableHasValueProperty(int var_type, bool vpi_vector);

// §37.17 detail 12: the vpiBit iterator applies only to logic, bit, packed
// struct, packed union, and packed array variables.
bool VpiBitIteratorApplies(int var_type, bool packed);

// §37.17 details 15 and 22: vpiRandType is one of vpiRand, vpiRandC,
// vpiNotRand.
bool VpiIsRandTypeValue(int value);

// §37.17 detail 16: vpiIsRandomized reports whether a random variable is
// currently active for randomization.
bool VpiIsRandomized(bool active_for_randomization);

// §37.17 detail 21: vpiArrayType is one of vpiStaticArray, vpiDynamicArray,
// vpiAssocArray, vpiQueueArray.
bool VpiIsArrayTypeValue(int value);

// §37.17 detail 20: the inputs the scalar/vector rules read for a variable.
struct VpiScalarVectorQuery {
  int var_type = 0;
  bool has_packed_dimension = false;  // bit/logic var: any packed dimensions
  bool packed = false;                // struct/union var: packed vs unpacked
  bool base_is_scalar = false;        // enum var: base typespec's vpiScalar
  bool base_is_vector = false;        // enum var: base typespec's vpiVector
  bool element_is_scalar = false;     // array var: an element's vpiScalar
  bool element_is_vector = false;     // array var: an element's vpiVector
};

// §37.17 detail 20: vpiScalar for a variable. A scalar bit/logic var (no packed
// dimension) and a var bit are scalars; an enum var defers to its base
// typespec; an array var defers to an element; every other variable is not a
// scalar.
bool VpiVariableScalar(const VpiScalarVectorQuery& query);

// §37.17 detail 20: vpiVector for a variable. A packed bit/logic var, a packed
// struct/union/array var, and the integer-typed vars are vectors; an enum var
// defers to its base typespec; an array var defers to an element; every other
// variable is not a vector.
bool VpiVariableVector(const VpiScalarVectorQuery& query);

// §37.17 detail 24: vpiVisibility of a variable. A class member reports its
// declared visibility (vpiLocalVis, vpiProtectedVis, or vpiPublicVis); a member
// that is neither local nor protected - and any non-class-member variable -
// reports vpiPublicVis.
int VpiVariableVisibility(bool is_class_member, int declared_visibility);

// §37.41 detail 4: vpiVisibility of a task or function. A class member (a
// method) reports its declared visibility (vpiLocalVis, vpiProtectedVis, or
// vpiPublicVis); a member that is neither local nor protected - and any task or
// function that is not a class member - reports vpiPublicVis.
int VpiTaskFuncVisibility(bool is_class_member, int declared_visibility);

// §37.17 detail 25: vpiFullName for a class data member. A non-static member
// has none (the empty string marks its absence); a static member's full name is
// the hierarchical path written through its "class defn", e.g.
// "top.Packet::Id".
std::string VpiClassMemberFullName(bool is_static, std::string_view scope_path,
                                   std::string_view class_defn,
                                   std::string_view member);

// §37.17 detail 26: a candidate vpiParent prefix object, in prefix order
// (rightmost/innermost first). A prefix qualifies when it is a
// struct/union/class variable, a struct/union member or class data member, or
// the largest containing packed or unpacked array object; otherwise its handle
// is null.
struct VpiParentPrefix {
  bool qualifies = false;
  VpiHandle handle = nullptr;
};

// §37.17 detail 26: vpiParent of a variable. Scanning the prefixes rightmost to
// leftmost, the first qualifying prefix is returned; NULL when none qualifies.
VpiHandle VpiVariableParent(const std::vector<VpiParentPrefix>& prefixes);

// §37.17 detail 26: among a run of nested array prefixes for one array object
// (given innermost first), vpiParent reports the largest (outermost) containing
// array - the last one - or null when there are none.
VpiHandle VpiLargestContainingArray(
    const std::vector<VpiHandle>& nested_innermost_first);

// §37.17 detail 27: the inputs vpiConstantSelect reads for a var bit or other
// variable.
struct VpiConstantSelectQuery {
  bool has_static_lifetime = false;
  bool has_parent = false;            // vpiParent != NULL
  bool all_indices_constant = false;  // every index is elaboration-constant
  bool all_elements_static_members = false;  // struct/union members or packed/
                                             // unpacked array elements with
                                             // static bounds
};

// §37.17 detail 27: vpiConstantSelect. TRUE when the variable has static
// lifetime and no parent, or when every index expression is an elaboration-time
// constant and every selected element is a struct/union member or a
// packed/unpacked array element with static bounds; FALSE otherwise.
bool VpiConstantSelect(const VpiConstantSelectQuery& query);

// §37.17 detail 28: the components of a member variable's name. The
// struct/union/ class-var prefixes run outermost first; the object's own
// index/slice (if any) is carried separately so it can be appended to all three
// name forms.
struct VpiVariableNameParts {
  std::string top_scope;
  std::vector<std::string> member_prefixes;
  std::string member;
  std::string index_suffix;
};

// §37.17 detail 28: vpiName - the leaf member with its own index/slice but none
// of its struct/union/class-var prefixes.
std::string VpiVariableName(const VpiVariableNameParts& parts);

// §37.17 detail 28: vpiDecompile - the prefixes joined to the member (and its
// index/slice) without the top-level scope, so it resolves for any
// non-top-level scope context.
std::string VpiVariableDecompile(const VpiVariableNameParts& parts);

// §37.17 detail 28: vpiFullName - the top-level scope prefixed to the decompile
// form.
std::string VpiVariableFullName(const VpiVariableNameParts& parts);

// ===========================================================================
// §37.18 Packed array variables. A vpiPackedArrayVar models a packed array of
// packed struct var, union var, or enum var objects. The size/vector/struct-
// union-member rules it cites are carried by the §37.17 variable helpers above;
// the relations and property below are §37.18's own normative details. The
// vpiElement and vpiIndex relations are recognized in VpiContext::Iterate
// rather than through a standalone iterator helper.
// ===========================================================================

// §37.18 detail 3: the member kinds a packed array variable's vpiElement
// transition reaches - a struct var, union var, enum var, or (for a
// multidimensioned packed array) another packed array var. Used to collect a
// packed array var's subelements one dimension level at a time.
bool VpiIsPackedArrayVarElementType(int type);

// §37.18 detail 4: vpiPackedArrayMember is TRUE for a struct var, union var,
// enum var, or packed array var whose vpiParent prefix is a packed array var,
// and FALSE for every other variable.
bool VpiVariableIsPackedArrayMember(VpiHandle var);

// ===========================================================================
// §37.19 Variable select. A var select is a variable reference qualified by one
// or more index expressions (vpiIndex) that reach into an unpacked array var
// (its vpiParent). Its name/full name (§37.17 detail 28), size (§37.17 detail
// 10), value (§38.34) and typespec relations are the generic variable
// machinery; the one normative detail owned here is when the var select's
// vpiConstantSelect property is TRUE.
// ===========================================================================

// §37.19 detail 1: the inputs vpiConstantSelect reads for a var select.
struct VpiVarSelectConstantSelectQuery {
  bool all_indices_constant = false;      // every index expression of the
                                          // select is an elaboration-time
                                          // constant expression
  bool parent_is_unpacked_static_array =  // the select's parent is an
      false;                              // unpacked array with static bounds
  bool parent_constant_select = false;    // vpiConstantSelect is TRUE for
                                          // the select's parent
};

// §37.19 detail 1: vpiConstantSelect of a var select. TRUE only when every
// index expression of the select is an elaboration-time constant, the parent is
// an unpacked array with static bounds, and vpiConstantSelect is itself TRUE
// for that parent; otherwise FALSE.
bool VpiVarSelectConstantSelect(const VpiVarSelectConstantSelectQuery& query);

// ===========================================================================
// §37.25 Typespec. The VPI object model for a type specification. Each helper
// applies one of the clause's numbered "Details"; the figure's range relations
// route through §37.22 and a member's expr role reuses §37.59's expr class. The
// figure attributes that carry no numbered Detail (vpiTagged/vpiSoft/vpiPacked/
// vpiVector/vpiArrayType/vpiRandType) are defined by §37.26 and §37.17, not
// here.
// ===========================================================================

// §37.25: the object-type codes the data model groups under the typespec class
// - every "... typespec" node of Figure 37.25, plus an unresolved type
// parameter, which acts as a typespec (detail 11). Used to tell a member's
// typespec child from its default-value expr child.
bool VpiIsTypespecType(int type);

// §37.25 detail 1: vpiName of a typespec. A typespec that denotes a
// user-defined typedef reports that typedef's name (which may be the empty
// string for a field defined inline, detail 5); a class typespec always reports
// the class name; every SystemVerilog built-in type reports NULL.
const char* VpiTypespecName(int ts_type, bool denotes_user_typedef,
                            const char* typedef_name, const char* class_name);

// §37.25 detail 1: vpiTypedefAlias of a typespec. A typespec whose typedef
// creates an alias of another typedef hands back a handle to the aliased
// typedef; a typespec that is not such an alias reports NULL.
VpiHandle VpiTypespecTypedefAlias(bool is_alias, VpiHandle aliased_typedef);

// §37.25 detail 2: vpiIndexTypespec of a typespec. The relation exists only on
// an associative-array typespec, where it yields the type used as the array
// key; a wildcard index type (see 7.8.1) yields NULL, and so does any typespec
// that is not an associative array.
VpiHandle VpiTypespecIndexTypespec(bool is_assoc_array_typespec,
                                   bool wildcard_index, VpiHandle key_typespec);

// §37.25 detail 3: the members vpi_iterate(vpiTypespecMember, typespec) walks.
// Only a struct or union typespec has members; every other typespec kind yields
// none.
std::vector<VpiHandle> VpiTypespecMembers(
    int ts_type, const std::vector<VpiHandle>& members);

// §37.25 detail 3: the typespec relation of a struct/union member indicates the
// member's type - the member's typespec child.
VpiHandle VpiTypespecMemberTypespec(VpiHandle member);

// §37.25 detail 4: vpiName of a typespec member is the member's own name, not
// the name of the member's typespec.
const char* VpiTypespecMemberName(VpiHandle member);

// §37.25 detail 7: the expr of a typespec member is the explicit default value
// of the corresponding member of an unpacked structure (see 7.2), reached as
// the member's expr child; a member with no default reports NULL.
VpiHandle VpiTypespecMemberDefaultExpr(VpiHandle member);

// §37.25 detail 8: vpi_handle(vpiElemTypespec, typespec) unwinds one array
// dimension at a time. A typespec that still has at least one range hands back
// the element typespec with its leftmost range removed; a typespec with no
// ranges present yields NULL.
VpiHandle VpiTypespecElemTypespec(bool has_ranges, VpiHandle element_typespec);

// §37.25 detail 10 (woven with §37.22): the ranges vpi_iterate(vpiRange,
// typespec) returns, one per dimension from leftmost to rightmost. For an array
// typespec these are the unpacked ranges; for a bit or logic typespec they are
// the packed ranges. A dynamic-array, queue, or associative dimension
// contributes an empty range.
std::vector<VpiRangeDesc> VpiTypespecRanges(
    const std::vector<VpiArrayDimension>& dims);

// §37.25 detail 9: vpiLeftRange of a typespec - the left bound of its leftmost
// dimension (the leftmost packed dimension of a logic/bit/packed-array
// typespec, the leftmost unpacked dimension of an array typespec). NULL when
// there is no dimension or that leftmost range is empty (§37.22).
VpiHandle VpiTypespecLeftRange(const std::vector<VpiArrayDimension>& dims);

// §37.25 detail 9: vpiRightRange of a typespec, the mirror of
// VpiTypespecLeftRange.
VpiHandle VpiTypespecRightRange(const std::vector<VpiArrayDimension>& dims);

// §37.25 detail 11: in a context where a type parameter has not been resolved,
// the type parameter itself acts as the typespec. Returns the resolved typespec
// when one exists, otherwise the type parameter handle itself.
VpiHandle VpiTypespecForTypeParameter(VpiHandle type_parameter,
                                      VpiHandle resolved_typespec);

// ===========================================================================
// §37.26 Structures and unions. The VPI object model for a structure or union
// declared as a variable (struct/union var) or as a net (struct/union net).
// Each is reached from its parent and iterates to its member variables or nets
// (vpiParent/vpiMember), and carries the Boolean figure properties vpiPacked,
// vpiTagged, and vpiSoft. Those relations and properties are served by the
// generic object-model machinery once an object's fields and children are set;
// the clause's one numbered rule (detail 1) is the value-access restriction the
// helpers below recognise.
// ===========================================================================

// ===========================================================================
// §37.21 Variable drivers and loads. The vpiDriver and vpiLoad edges relate a
// variable to the objects that drive it and the objects that read it. A driver
// or load is not a child whose own type is literally vpiDriver/vpiLoad; it is
// one of the driving/reading object kinds the figure lists, so the iteration is
// recognised through these classifiers.
// ===========================================================================

// §37.21 (figure, variable drivers): the object kinds that drive a variable - a
// port, a force, a continuous assignment (a whole continuous assignment or a
// single bit of one), or a procedural assignment statement.
bool VpiIsVariableDriverType(int type);

// §37.21 (figure, variable loads): the object kinds that read a variable. They
// are the driver kinds without a port: an assignment statement, a force, and a
// continuous assignment (whole or single bit). A port appears only as a driver.
bool VpiIsVariableLoadType(int type);

// ===========================================================================
// §37.46 Net drivers and loads. The vpiDriver and vpiLoad edges relate a net to
// the objects that drive it and the objects that load (read) it. As in §37.21 a
// driver/load is not a child whose own type is literally vpiDriver/vpiLoad; it
// is one of the object kinds the figure lists, recognised through the
// classifiers below. The net case differs from the variable case: an assignment
// statement loads but does not drive a net, and a port loads a net only through
// the complex-expression rule of detail 1, recognised separately below.
// ===========================================================================

// §37.46 (figure, net drivers): the object kinds that drive a net - a port, a
// force, a delay terminal, a continuous assignment (whole or single bit), or a
// primitive terminal.
bool VpiIsNetDriverType(int type);

// §37.46 (figure, net loads): the object kinds that load a net - a delay
// terminal, an assignment statement, a force, a continuous assignment (whole or
// single bit), or a primitive terminal. A port loads a net only through the
// complex-expression rule of detail 1, so it is not part of this set.
bool VpiIsNetLoadType(int type);

// §37.46 detail 1: whether an input port carries a complex expression that
// loads the nets it reads, making the port itself a load. The connection on the
// port (its vpiHighConn) must be a complex expression - an operation rather
// than a simple reference - and must not be a concatenation, whose operands
// connect their nets individually. Only an input port loads this way; the
// complex expression itself is reached through vpi_handle(vpiHighConn, port)
// (§37.14).
bool VpiPortIsComplexExpressionLoad(VpiHandle port);

// §37.26 (figure): the four object kinds the Structures-and-unions figure
// models - a structure or union declared as a variable, and a structure or
// union declared as a net. Used to recognise an entire structure/union object.
bool VpiIsStructOrUnionType(int type);

// §37.26 detail 1: whether an object is an entire unpacked structure or
// unpacked union - one whose value vpi_get_value()/vpi_put_value() cannot
// access. A packed struct/union (vpiPacked true) has a single vector value and
// stays accessible; only the unpacked aggregate is off-limits, so the rule is
// the struct/union object kinds restricted to the unpacked case.
bool VpiIsEntireUnpackedStructOrUnion(int type, bool packed);

}  // namespace delta
