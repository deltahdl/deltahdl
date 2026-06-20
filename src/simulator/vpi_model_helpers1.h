#pragma once

#include <string>
#include <string_view>
#include <vector>

#include "simulator/vpi_constants.h"
#include "simulator/vpi_object.h"

namespace delta {

// §37.10 details 1 and 10: one entry per typedef/nettype an instance could
// report. The vpiTypedef and vpiNetTypedef iterations return only entries that
// are user-defined (not built-in) AND explicitly declared inside the instance,
// so both flags gate visibility.
struct VpiTypeDeclEntry {
  std::string name;
  bool user_defined = false;
  bool declared_in_instance = false;
};

// §37.10 detail 1: the vpiTypedef iteration returns the user-defined typespecs
// that have typedefs explicitly declared in the instance, dropping every other
// entry while preserving declaration order.
std::vector<const VpiTypeDeclEntry*> VpiInstanceTypedefs(
    const std::vector<VpiTypeDeclEntry>& entries);

// §37.10 detail 10: the vpiNetTypedef iteration returns the user-defined
// nettypes explicitly declared in the instance, with the same gating.
std::vector<const VpiTypeDeclEntry*> VpiInstanceNetTypedefs(
    const std::vector<VpiTypeDeclEntry>& entries);

// §37.10 detail 3: the kinds of object that count as an instance, i.e. the
// scopes a vpiInstance relation may resolve to.
bool VpiIsInstanceType(int type);

// §37.10 detail 3: vpiInstance returns the immediate (nearest enclosing)
// instance an object is instantiated in, or null when none encloses it.
VpiHandle VpiInstanceOf(VpiHandle obj);

// §37.10 detail 2: vpiModule returns the nearest enclosing module when the
// object is inside a module instance, otherwise null.
VpiHandle VpiModuleOf(VpiHandle obj);

// §37.10 detail 4: the vpiMemory iteration reports array variable objects
// rather than vpiMemory objects, so the item type is the array-variable kind.
int VpiMemoryIterationItemType();

// §37.10 detail 5: vpiFullName construction. Objects within a compilation unit
// are prefixed with the "$unit::" scope name.
std::string VpiCompilationUnitFullName(std::string_view object_path);

// §37.10 detail 5: a package's full name is its own name and ends with the
// "::" package separator so a module and a like-named package stay distinct.
std::string VpiPackageFullName(std::string_view package_name);

// §37.10 detail 5: an object declared in a package is named with the package
// name, the "::" separator, then the member path.
std::string VpiPackageMemberFullName(std::string_view package_name,
                                     std::string_view member_path);

// §37.10 detail 5: the separator placed before a name component. A component
// immediately following a package or class-definition scope uses "::"; every
// other boundary uses ".".
std::string_view VpiNameSeparator(bool package_or_class_defn_boundary);

// §37.10 detail 6: vpi_handle_by_name() must not reach imported items or
// objects that exist within a compilation unit. Returns false for those.
bool VpiHandleByNameAccessible(const VpiObject& obj);

// §37.10 detail 7: the smallest time precision across the supplied modules.
// With no modules there is nothing to report, so the result is zero.
int VpiSmallestTimePrecision(const std::vector<int>& precisions);

// §37.49: the assertion class groups the concurrent
// assert/assume/cover/restrict kinds, the immediate assert/assume/cover kinds,
// and sequence and property instances. An object is an assertion exactly when
// its type is one of these.
bool VpiIsAssertionType(int type);

// §37.34 detail 5: a constraint item is the abstract grouping of the kinds the
// vpiConstraintItem iteration reaches - a constraint ordering or a constraint
// expression. An object qualifies as a constraint item exactly when its type is
// one of these.
bool VpiIsConstraintItemType(int type);

// §37.38 detail 3: a constraint-expression container is the kind of constraint
// expression whose vpiConstraintExpr iteration reaches the nested expressions
// it holds - an implication, a constraint if, a constraint if-else, or a
// foreach constraint. An object qualifies exactly when its type is one of
// these.
bool VpiIsConstraintExprContainerType(int type);

// §37.31 detail 1: a class method is the kind of object the vpiMethods
// iteration of a class defn reaches - a task or a function declared as a class
// item. An object qualifies as a method exactly when its type is one of these.
bool VpiIsClassMethodType(int type);

// §37.31 detail 2: the variable/event grouping for which a value obtained from
// a class defn handle is not accessible - the variables node, the concrete
// variable kinds, a class variable, and the named event / named event array.
bool VpiIsClassMemberValueType(int type);

// §37.49: the clocking block governing a concurrent assertion, traversed with
// vpi_handle(vpiClockingBlock, ...). Returns null when no clocking block is
// associated with the assertion.
VpiHandle VpiAssertionClockingBlock(VpiHandle assertion);

// §37.50: the concurrent-assertion class groups the four directive kinds the
// diagram draws inside its dashed box - assert, assume, cover, and restrict. An
// object is a concurrent assertion exactly when its type is one of these. (This
// is the concurrent subset of §37.49's broader assertion class, which also
// covers the immediate kinds and sequence/property instances.)
bool VpiIsConcurrentAssertionType(int type);

// §37.50: the kinds the concurrent assertion's vpiProperty relation may reach -
// a property instance or a property specification. Any other kind is not a
// concurrent assertion's property.
bool VpiIsConcurrentAssertionPropertyType(int type);

// §37.50: the property a concurrent assertion traverses to through vpiProperty
// - its first property-instance/specification child; null for a null handle or
// an assertion with no property attached.
VpiHandle VpiConcurrentAssertionProperty(VpiHandle assertion);

// §37.50 (detail 1): the clocking event a concurrent assertion is evaluated on,
// reached through vpiClockingEvent and modeled as its event-control child. This
// is always the actual event the assertion runs on, whether it was written
// explicitly or inferred from context; vpiIsClockInferred (a separate Boolean)
// records which form produced it. Null when no clocking event is attached.
VpiHandle VpiConcurrentAssertionClockingEvent(VpiHandle assertion);

// §37.50 (-> stmt / detail 2): whether a concurrent assertion kind carries a
// pass action statement. assert, assume and cover do; a restrict has no pass
// action statement.
bool VpiConcurrentAssertionHasPassStmt(int type);

// §37.50 (vpiElseStmt / detail 2): whether a concurrent assertion kind carries
// an else (fail) action statement. Only assert and assume do; a cover has no
// else statement and a restrict has no fail action statement.
bool VpiConcurrentAssertionHasElseStmt(int type);

// §37.50: the pass action statement a concurrent assertion traverses to through
// vpiStmt - its first statement child; null when none is attached (for example
// a restrict, which has no pass action statement).
VpiHandle VpiConcurrentAssertionStmt(VpiHandle assertion);

// §37.50: the else (fail) action statement a concurrent assertion traverses to
// through vpiElseStmt - its first else-statement child; null when none is
// attached (a cover or restrict has none).
VpiHandle VpiConcurrentAssertionElseStmt(VpiHandle assertion);

// §37.50 (detail 2): whether a concurrent assertion kind is simulated and so
// generates run-time information. Every kind is, except restrict, which is not
// simulated and hence generates no run-time information.
bool VpiConcurrentAssertionIsSimulated(int type);

// §37.55: the immediate-assertion class groups the three immediate directive
// kinds the diagram draws - immediate assert, immediate assume, and immediate
// cover. An object is an immediate assertion exactly when its type is one of
// these. (This is the immediate counterpart of §37.50's concurrent assertions;
// both are part of §37.49's broader assertion class.)
bool VpiIsImmediateAssertionType(int type);

// §37.55 (vpiElseStmt): whether an immediate-assertion kind carries an else
// (fail) action statement. An immediate assert and an immediate assume do; an
// immediate cover has no else statement (the diagram draws it with a single,
// unconditional action block).
bool VpiImmediateAssertionHasElseStmt(int type);

// §37.55: the asserted expression an immediate assertion traverses to through
// vpiExpr - its first expression child; null for a null handle or an assertion
// with no expression attached.
VpiHandle VpiImmediateAssertionExpr(VpiHandle assertion);

// §37.55: the pass action statement an immediate assertion traverses to through
// vpiStmt - its first statement child; null when none is attached.
VpiHandle VpiImmediateAssertionStmt(VpiHandle assertion);

// §37.55 (vpiElseStmt): the else (fail) action statement an immediate assert or
// assume traverses to through vpiElseStmt - its first else-statement child;
// null when none is attached (an immediate cover never has one).
VpiHandle VpiImmediateAssertionElseStmt(VpiHandle assertion);

// §37.54 (D1): the sequence-expr class groups the kinds the diagram draws under
// it - an operation, a sequence instance, a distribution, and a bare boolean
// expression (a constant or a reference used directly as a sequence). An object
// is a sequence expression exactly when its type is one of these.
bool VpiIsSequenceExprType(int type);

// §37.54 detail 2: the operation types a sequence expression's vpiOpType may
// report - the composite and/or, intersect, first-match, throughout, within,
// the unary and binary cycle delays, and the three repeat operators. Every
// other operator value is rejected.
bool VpiIsSequenceExprOpType(int op);

// §37.54 detail 3a: the operands of a unary cycle-delay (##) operation, in the
// order vpiOperand presents them: the sequence, the left range, then the right
// range. The right range is reported only when it differs from the left range;
// passing the same handle (or null) for the right range models a range whose
// bounds coincide and yields just the sequence and the left range.
std::vector<VpiHandle> VpiUnaryCycleDelayOperands(VpiHandle sequence,
                                                  VpiHandle left_range,
                                                  VpiHandle right_range);

// §37.54 detail 3b: the operands of a binary cycle-delay (##) operation: the
// left-hand side sequence, the right-hand side sequence, the left range, then
// the right range. The right range is reported only when it differs from the
// left range.
std::vector<VpiHandle> VpiCycleDelayOperands(VpiHandle lhs_sequence,
                                             VpiHandle rhs_sequence,
                                             VpiHandle left_range,
                                             VpiHandle right_range);

// §37.54 detail 3c: the operands of any repeat operation ([*], [=], [->]): the
// repeated sequence, the left repeat bound, then the right repeat bound. The
// right bound is reported only when it differs from the left bound.
std::vector<VpiHandle> VpiRepeatOperands(VpiHandle sequence,
                                         VpiHandle left_bound,
                                         VpiHandle right_bound);

// §37.54 detail 1: a sequence formal as seen by the argument iteration. A
// formal may carry a default value (null when it has none) that is used as the
// argument when an instantiation does not provide one.
struct VpiSequenceFormal {
  VpiHandle default_value = nullptr;
};

// §37.54 detail 1: the arguments the vpiArgument iteration returns for a
// sequence instance, in formal-declaration order. `provided` is parallel to
// `formals`; a null entry means the instantiation omitted that argument, so the
// formal's default value is substituted in its place (preserving the order so
// each argument lines up with its formal).
std::vector<VpiHandle> VpiSequenceInstArguments(
    const std::vector<VpiSequenceFormal>& formals,
    const std::vector<VpiHandle>& provided);

// §37.54 (D5): the kinds an argument of a sequence instance may be - a named
// event or a sequence expression. Any other kind is not a valid argument.
bool VpiIsSequenceArgumentType(int type);

// §37.54 (D4): the sequence declaration a sequence instance instantiates,
// traversed to its vpiSequenceDecl child. Returns null for a null handle or an
// instance with no declaration attached.
VpiHandle VpiSequenceInstDecl(VpiHandle sequence_inst);

// §37.54 (D6): the match items a sequence's bare boolean expression may carry
// are assignments and task/function calls. Other object kinds are not match
// items.
bool VpiIsMatchItemType(int type);

// §37.54 (D6): the match items reachable from a bare expression through the
// vpiMatchItem iteration - its assignment/tf-call children, in order. A null
// handle yields no items.
std::vector<VpiHandle> VpiExprMatchItems(VpiHandle expr);

// §37.52: the property-expr class groups the kinds the diagram draws under it -
// an operation, a multiclock sequence expression, a property instance, a
// clocked property, and a case property. (A sequence expression is also a
// property expression; classifying the sequence-expr kinds is the sequence-expr
// class's concern.) The class selector itself is not one of these member kinds.
bool VpiIsPropertyExprType(int type);

// §37.52 detail 2: the property operators a property expr's operation may
// report through vpi_get(vpiOpType). Every other operator value is not a
// property operator.
bool VpiIsPropertyExprOpType(int op);

// §37.52 detail 2 (vpiNexttimeOp exception): the operands of a nexttime
// operation in the order vpiOperand presents them - the property, then the
// constant. The constant is reported only when it differs from 1.
std::vector<VpiHandle> VpiNexttimeOperands(VpiHandle property,
                                           VpiHandle constant,
                                           bool constant_differs_from_one);

// §37.52 detail 2 (vpiAlwaysOp/vpiEventuallyOp exception): the operands of an
// always or eventually operation - the property, then the left and right range
// bounds. A null bound is omitted, so an unranged operator yields just the
// property.
std::vector<VpiHandle> VpiAlwaysEventuallyOperands(VpiHandle property,
                                                   VpiHandle left_range,
                                                   VpiHandle right_range);

// §37.52 detail 3: vpiOpStrong is meaningful only for these property operators
// (it is also meaningful for a sequence expression, whose strength the
// sequence-expr class governs). For every other operator it does not apply.
bool VpiIsOpStrongValidOp(int op);

// §37.52 detail 1: the value of a property variable cannot be accessed through
// VPI, so this is always false.
bool VpiIsPropertyVariableValueAccessible();

// §37.52 detail 4: the case conditions a case property item groups - its
// condition members, each of which branches to the item's property statement,
// in order. A case property item's property statement (the diagram's case
// property item -> property expr edge) is excluded. The default case item has
// no condition expression, so it groups none (detail 5).
std::vector<VpiHandle> VpiCaseItemConditions(VpiHandle case_item);

// §37.72: the object kinds a case item's match expressions may reach. The
// diagram draws the case item's vpiExpr edge to both the pattern grouping and a
// plain expr, so a condition is one of the pattern kinds (any/tagged/struct
// pattern, or a bare pattern) or an ordinary expression.
bool VpiIsCaseItemConditionType(int type);

// §37.72 detail 1: the case conditions a (statement) case item groups - its
// match-expression members, each of which branches to the item's statement, in
// declaration order. The statement reached through the item's -> stmt edge is
// not a condition. The default case item has no condition expression, so it
// groups none (detail 2).
std::vector<VpiHandle> VpiCaseItemMatchExprs(VpiHandle case_item);

// §37.52: the kinds the property-spec/property-expr disable-condition relation
// may reach - a bare expression or a distribution. (A property instance's
// disable condition reaches only an expression; see §37.51.)
bool VpiIsDisableConditionType(int type);

// §37.52: the clocking event a property spec or clocked property traverses to
// through vpiClockingEvent (the diagram's -> expr edge), modeled as the
// object's event-control child; null when none is present. §37.56's clocked seq
// shares this relation (its own vpiClockingEvent -> expr edge has the same
// shape).
VpiHandle VpiClockingEvent(VpiHandle obj);

// §37.52: the property expression reached through a "-> property expr" edge (a
// property spec, a clocked property, or a case property item branch) - the
// object's first property-expr-kind child; null when none is present.
VpiHandle VpiPropertyExprChild(VpiHandle obj);

// §37.51 detail 1: the formals a property declaration declares as the
// vpiPropFormalDecl iteration yields them - its vpiPropFormalDecl children in
// declaration order. A null handle yields none.
std::vector<VpiHandle> VpiPropFormals(VpiHandle property_decl);

// §37.51 detail 5: a property formal's vpiDirection. A formal that is a local
// variable argument reports vpiInput; every other formal reports
// vpiNoDirection.
int VpiPropFormalDirection(bool is_local_variable_argument);

// §37.51 detail 3: the typespec of a property formal (its vpiTypespec child),
// or null when the formal is untyped.
VpiHandle VpiPropFormalTypespec(VpiHandle formal);

// §37.51 detail 4: the initialization expression of a property formal, reached
// through vpiExpr. The diagram draws this target as a named event or a property
// expression; null when the formal has no initialization expression.
VpiHandle VpiPropFormalInitExpr(VpiHandle formal);

// §37.51 detail 2: a property formal as seen by the property-instance argument
// iteration. A formal may carry a default value (null when none) that is used
// as the argument when an instantiation does not provide one.
struct VpiPropertyFormal {
  VpiHandle default_value = nullptr;
};

// §37.51 detail 2: the arguments the vpiArgument iteration returns for a
// property instance, in formal-declaration order so each argument corresponds
// to its formal. `provided` is parallel to `formals`; a null entry means the
// instantiation omitted that argument, so the formal's default value is used in
// its place, preserving the order so each argument lines up with its formal.
std::vector<VpiHandle> VpiPropertyInstArguments(
    const std::vector<VpiPropertyFormal>& formals,
    const std::vector<VpiHandle>& provided);

// §37.51: the kinds an argument of a property instance may be (the diagram's
// vpiArgument -> property expr | named event) - a named event or a property
// expression. Any other kind is not a valid argument.
bool VpiIsPropertyArgumentType(int type);

// §37.51: the property declaration a property instance instantiates (the
// diagram's property inst -> property decl edge), its vpiPropertyDecl child;
// null for a null handle or an instance with no declaration attached.
VpiHandle VpiPropertyInstDecl(VpiHandle property_inst);

// §37.56: the clocked-seq members of a multiclock sequence expression. The
// diagram's double (one-to-many) tagless arrow is the vpiClockedSeq iteration,
// so this returns the multiclock sequence expression's vpiClockedSeq children
// in order, dropping anything else. A null handle yields none.
std::vector<VpiHandle> VpiMulticlockSequenceClockedSeqs(
    VpiHandle multiclock_seq);

// §37.56: the sequence expression a clocked seq clocks (the diagram's single
// tagless arrow, vpi_handle(vpiSequenceExpr, ...)). A clocked seq pairs one
// clocking event with one sequence expression, so this is the clocked seq's
// first sequence-expr-kind child (classified by VpiIsSequenceExprType); null
// for a null handle or a clocked seq with no sequence expression attached. The
// clocking-event half of the pair is reached through VpiClockingEvent.
VpiHandle VpiClockedSeqSequenceExpr(VpiHandle clocked_seq);

// §37.53 detail 1: the formals a sequence declaration declares as the
// vpiSeqFormalDecl iteration yields them - its vpiSeqFormalDecl children in
// declaration order. A null handle yields none.
std::vector<VpiHandle> VpiSeqFormals(VpiHandle sequence_decl);

// §37.53: the body of a sequence declaration, reached through vpiExpr. The
// diagram draws its target as a sequence expression (the sequence-expr class,
// §37.54) or a multiclock sequence expression (§37.56). Returns the object's
// first such child, or null when none is present.
VpiHandle VpiSeqDeclBodyExpr(VpiHandle sequence_decl);

// §37.53 detail 4: a seq formal decl's vpiDirection. A formal that is not a
// local variable argument has no direction (vpiNoDirection); a local variable
// argument reports its declared direction, one of vpiInput, vpiOutput, or
// vpiInout. (This is the sequence analog of §37.51's property formal, which
// only ever reports vpiInput.)
int VpiSeqFormalDirection(bool is_local_variable_argument, int local_direction);

// §37.53 detail 2: the typespec of a seq formal decl (its vpiTypespec child),
// or null when the formal is untyped.
VpiHandle VpiSeqFormalTypespec(VpiHandle formal);

// §37.53 detail 3: the initialization expression of a seq formal decl, reached
// through vpiExpr. The diagram draws its target as a named event or a sequence
// expression (§37.54); null when the formal has no initialization expression.
VpiHandle VpiSeqFormalInitExpr(VpiHandle formal);

// §37.57 detail 1: a let formal as seen by the let expression's argument
// iteration. A formal may carry a default value (null when it has none) that
// stands in as the argument when an instantiation does not supply one.
struct VpiLetFormal {
  VpiHandle default_value = nullptr;
};

// §37.57 detail 1: the arguments the vpiArgument iteration returns for a let
// expression, in the order the let's formals are declared so each argument can
// be matched to its formal. `provided` is parallel to `formals`; a null entry
// means the instantiation omitted that argument, so the formal's default value
// is substituted in its place, keeping the declaration order intact.
std::vector<VpiHandle> VpiLetExprArguments(
    const std::vector<VpiLetFormal>& formals,
    const std::vector<VpiHandle>& provided);

// ===========================================================================
// §37.42 Task and function call. The VPI object model for a tf call - the task
// call, function call, method task/func call, and system task/func call the
// diagram groups under "tf call". A call iterates its arguments (vpiArgument);
// a method call additionally reaches the object it is applied to (vpiPrefix)
// and, for the methods that take one, a with clause (vpiWith). The helpers and
// the dispatch wiring below carry the subclause's numbered Details.
// ===========================================================================

// §37.42: the call kinds the tf call class groups - a task call, a function
// call, a method task/func call, and a system task/func call.
bool VpiIsTfCallType(int type);

// §37.42 details 1, 2, 11: the method-call kinds (method func call, method task
// call). The vpiPrefix and vpiWith relations apply only to these, as does the
// built-in-method NULL rule for vpiFunction/vpiTask.
bool VpiIsMethodCallType(int type);

// §37.42: the object kinds the vpiArgument relation reaches from a tf call - an
// expression, an interface expression, a scope, a primitive, a named event, or
// a named event array. Used to collect a call's arguments when iterating
// vpiArgument: an argument is found by being one of these kinds, not by being a
// child whose own type happens to be vpiArgument.
bool VpiIsTfCallArgumentType(int type);

// §37.42 detail 8: how an omitted (empty) call argument is represented - as an
// expression object of type vpiOperation whose vpiOpType is vpiNullOp. Sets
// those two fields on `arg` so vpi_get reports them.
void VpiMakeEmptyArgument(VpiHandle arg);

// §37.42 detail 8: how a call argument written as the special value `null` is
// represented - as an expression object of type vpiConstant whose vpiConstType
// is vpiNullConst. Sets those two fields on `arg` so vpi_get reports them.
void VpiMakeNullArgument(VpiHandle arg);

// ===========================================================================
// §37.58 Simple expressions. The VPI object model for a simple expression - a
// reference (net, variable, ref obj, parameter, spec param) or a select of one
// (var select, bit select). Its vpiUse relation reaches the terminals,
// statements, and continuous assignments that reference it; a bit-select also
// carries the vpiParent/vpiIndex relations, a name, and the vpiConstantSelect
// property. The generic naming and traversal machinery is supplied by §38.11
// and §38.18; the helpers below carry the subclause's three numbered Details.
// ===========================================================================

// §37.58 detail 1: whether a candidate use is reached by the vpiUse relation of
// a vector simple expression. It is, when the use references the vector itself
// or any of the vector's part-selects or bit-selects.
bool VpiSimpleExprVectorUseAccessesUse(bool references_vector,
                                       bool references_part_select_of_vector,
                                       bool references_bit_select_of_vector);

// §37.58 detail 2: whether a candidate use is reached by the vpiUse relation of
// a bit-select. It is, when the use references that specific bit, the parent
// vector, or a part-select of the parent that contains the bit.
bool VpiSimpleExprBitSelectUseAccessesUse(
    bool references_this_bit, bool references_parent_vector,
    bool references_part_select_containing_bit);

// §37.58 detail 3: vpiConstantSelect of a bit-select. TRUE only when every
// associated index expression is an elaboration-time constant and
// vpiConstantSelect is itself TRUE for the bit-select's parent; otherwise
// FALSE.
bool VpiSimpleExprBitSelectConstantSelect(bool all_indices_constant,
                                          bool parent_constant_select);

// ===========================================================================
// §37.61 Dynamic prefixing. The object model diagram draws a vpiPrefix relation
// from a dynamically prefixed object - a simple expression (a reference, a bit-
// select, a part-select, or an indexed part-select), a named event, a named
// event array, or a tf call - to the class var, virtual interface var, or
// clocking block that prefixes it; and gives those source objects one property
// edge, "-> has actual" (bool: vpiHasActual). The tf call's prefix is owned by
// §37.42; the helpers below carry §37.61's own normative details.
// ===========================================================================

// §37.61 detail 1: the object kinds that can carry a dynamic prefix and report
// it through vpiPrefix - the concrete simple-expression kinds (a reference and
// a bit-select), a part-select and an indexed part-select, a named event, and a
// named event array. A tf call is excluded: a method call's prefix is supplied
// by §37.42, so a tf call is not classified here. Scopes the vpiPrefix
// traversal so the relation is served only for the source kinds the diagram
// draws it from.
bool VpiIsDynamicPrefixSourceType(int type);

// §37.61 detail 3: whether a dynamically prefixed object has a corresponding
// actual, the value reported through vpiHasActual. `actual_origin` selects how
// the answer is fixed (a kVpiActual* provenance); `has_current_actual` is
// whether the object is bound to an actual at the current simulation time, used
// only when the provenance leaves the question to simulation time. A statically
// declared object in an elaborated context and an automatic variable obtained
// from a frame have an actual; an object obtained from a class defn, referenced
// relative to a class typespec, or automatically allocated from a task/function
// declaration does not.
bool VpiObjectHasActual(int actual_origin, bool has_current_actual);

// ===========================================================================
// §37.59 Expressions. The VPI object model for an expression. The expr class
// groups operations, constants, part-selects and indexed part-selects, the
// function/method-function/system-function calls and let expressions, and a
// simple expression (a reference). Every expression carries the vpiDecompile,
// vpiSize and value properties; an operation carries vpiOpType, a constant
// vpiConstType, and an indexed part-select vpiIndexedPartSelectType (all
// applied by VpiContext::Get). The helpers below carry the subclause's
// normative details.
// ===========================================================================

// §37.59: the kinds the expr class groups in the data model diagram - an
// operation, a constant, a part-select or indexed part-select, a
// func/method-func/ sys-func call, a let expression, and a reference (the
// concrete simple expression). Used to scope detail 8's protected-object
// carve-out (vpiSize stays accessible on a protected expression) and to
// classify diagram members.
bool VpiIsExprType(int type);

// §37.3.5: whether an expression has side effects when evaluated - true exactly
// when the object is non-null and carries the has_side_effects mark. The
// put_value index-expression check and any application that needs to ask the
// question share this single predicate, so the notion of "expression with side
// effects" is decided in one place.
bool VpiExpressionHasSideEffects(const VpiObject* obj);

// §37.3.4 (Delays and values): the object kinds whose delays are written within
// the SystemVerilog source and are therefore reachable as an expression through
// the vpiDelay relation - a net, a primitive, a module path, a timing check, or
// a continuous assignment. Other objects carry no source-written delay.
bool VpiObjectCarriesSourceDelay(int type);

// §37.3.4 (Delays and values): traversing vpiDelay from such an object reaches
// the expression that gives its source-specified delay. Modeled as the object's
// designated delay-expression pointer. NULL when the handle is null, is not a
// delay-carrying object kind, or carries no source delay.
VpiHandle VpiSourceDelayExpr(VpiHandle obj);

// §37.3.4 (Delays and values): the vpiDelay expression shall be either an
// expression that evaluates to a constant, when one delay is specified, or an
// operation, when more than one delay is specified; in the multiple-delay case
// the operation's vpiOpType shall be vpiListOp. Returns true iff the given
// expression is that multiple-delay vpiListOp operation form.
bool VpiSourceDelayExprIsListOp(VpiHandle expr);

// §37.60: the statement kinds the atomic stmt class groups in the object model
// diagram - the procedural control statements (if, if-else, while, repeat, the
// waits, case, for, the timing controls, the event statement, the assignments,
// deassign, the disables, the tf calls, forever, force, release, do-while, the
// expect/foreach/return statements, break, continue, the immediate assertions,
// and the null statement). Used to scope detail 1, which gives an atomic
// statement a single label edge: vpiName reports its label, or NULL when none.
bool VpiIsAtomicStmtType(int type);

// §37.64 Assignment detail 1: the vpiOpType an assignment object reports. A
// normal assignment - blocking "=" or nonblocking "<=" - reports
// vpiAssignmentOp. An assignment written with an assignment operator instead
// reports the operator combined with the assignment, following 11.4.1: "+="
// reports vpiAddOp, "-=" vpiSubOp, "<<<=" vpiArithLShiftOp, and so on.
// `assign_operator` is the source spelling of the operator ("=", "<=", "+=",
// ...). Any spelling that is not one of the assignment operators is treated as
// a normal assignment (vpiAssignmentOp).
int VpiAssignmentOpType(std::string_view assign_operator);

// §37.63 Process detail 1: whether `always_type` is a legal value of the
// vpiAlwaysType property. The property distinguishes the flavors of always
// procedure and is restricted to exactly four constants - vpiAlways,
// vpiAlwaysComb, vpiAlwaysFF, and vpiAlwaysLatch. Any other value (including
// the unset default carried by an initial or final process) is not an always
// type. Scopes vpi_get(vpiAlwaysType), which reports the value only when it is
// one of the four and vpiUndefined otherwise.
bool VpiIsAlwaysType(int always_type);

// §37.65 Event control detail 1: the statement an event control "@" reaches
// through vpiStmt. An event control associated with an assignment - the event
// control drawn on an assignment object (§37.64), recognized here by its parent
// being a vpiAssignment - always reports a null statement, because the
// assignment itself is the action and guards no separate statement. Any other
// event control reports its first statement child, or null when none is
// attached. Backs the public vpi_handle(vpiStmt, event_control) dispatch.
VpiHandle VpiEventControlStmt(VpiHandle event_control);

// §37.68 Delay control detail 1: the statement a delay control "#" reaches
// through vpiStmt. A delay control associated with an assignment - the delay
// control drawn on an assignment object (§37.64), recognized here by its parent
// being a vpiAssignment - always reports a null statement, because the
// assignment itself is the action and guards no separate statement. Any other
// delay control reports its first statement child, or null when none is
// attached. Backs the public vpi_handle(vpiStmt, delay_control) dispatch.
VpiHandle VpiDelayControlStmt(VpiHandle delay_control);

// §37.66 While, repeat: whether an object kind is one of the two looping
// statements the while/repeat diagram groups - a while statement or a repeat
// statement. Both reach a condition expression and a body statement through the
// same relations.
bool VpiIsWhileOrRepeatType(int type);

// §37.66 While, repeat: the controlling condition expression a while or repeat
// statement reaches through vpiCondition. The condition's own type is an
// expression kind rather than the vpiCondition relation tag, so it is found as
// the loop's first expression child; null when none is attached. Backs the
// public vpi_handle(vpiCondition, while/repeat) dispatch.
VpiHandle VpiLoopConditionExpr(VpiHandle loop);

// §37.67 Waits: whether an object kind is one of the wait statements the
// diagram groups under "waits" - a wait, an ordered wait, or a wait fork. The
// grouping shares a body statement (vpiStmt) and, for the wait and ordered
// wait, a controlling condition (vpiCondition).
bool VpiIsWaitType(int type);

// §37.67 Waits: the controlling condition a wait or ordered wait statement
// reaches through vpiCondition. The condition may be either an expression or a
// sequence instance; either way its own type is an expression/sequence kind
// rather than the vpiCondition relation tag, so it is found as the wait's first
// such child. Null when none is attached (as for a wait fork, which draws no
// condition edge). This is a dedicated helper rather than a vpi_handle dispatch
// case: the public vpiCondition dispatch is scoped to the loop statements of
// §37.66, which leaves a wait's condition to this helper.
VpiHandle VpiWaitConditionExpr(VpiHandle wait);

// §37.69 Repeat control: the count expression a repeat control reaches through
// its unlabeled edge to an expr (the vpiExpr relation) - the number of triggers
// of the intra-assignment repeat event control "repeat (n) @(event)". The
// count's own type is an expression kind (an operation, a constant, a
// reference, ...) rather than the vpiExpr relation tag, so it is found as the
// repeat control's first expression child; null when none is attached. The
// diagram's other unlabeled edge, to the event control, reaches an object whose
// own type is vpiEventControl and so is served by the generic traversal,
// needing no helper. Backs the public vpi_handle(vpiExpr, repeat_control)
// dispatch.
VpiHandle VpiRepeatControlExpr(VpiHandle repeat_control);

// §37.77 Disables: whether an object kind is one of the named scopes a disable
// statement may target - the four kinds the diagram groups at the far end of
// the disable's vpiExpr edge: a task, a function, a named begin block, or a
// named fork block.
bool VpiIsDisableTargetType(int type);

// §37.77 Disables: the named scope a disable statement reaches through vpiExpr
// - the task, function, named begin, or named fork it disables. The scope's own
// type is one of those kinds rather than the vpiExpr relation tag, so it is
// found as the disable's first disable-target child; null when none is
// attached. A disable fork (vpiDisableFork) draws no such edge - it disables
// the active process's children with no named operand - so this relation is
// scoped to the plain disable statement and a disable fork reports null. Backs
// the public vpi_handle(vpiExpr, disable) dispatch.
VpiHandle VpiDisableExpr(VpiHandle disable);

// §37.71 If, if-else: whether an object kind is one of the two conditional
// statements the if/if-else diagram groups - a plain if statement or an
// if-else statement. Both reach a controlling condition (vpiCondition) and a
// then-branch body (the generic vpiStmt edge); the if-else additionally reaches
// an else-branch body (vpiElseStmt).
bool VpiIsIfOrIfElseType(int type);

// §37.71 If, if-else: the controlling condition expression an if or if-else
// statement reaches through vpiCondition. The condition's own type is an
// expression kind rather than the vpiCondition relation tag, so it is found as
// the statement's first expression child; null when none is attached. Backs the
// public vpi_handle(vpiCondition, if/if-else) dispatch.
VpiHandle VpiIfConditionExpr(VpiHandle if_stmt);

// §37.71 If, if-else: the else-branch body an if-else statement reaches through
// vpiElseStmt. The then-branch and the else-branch are both body statements;
// the then-branch is served by the generic vpiStmt traversal (the first body
// child) and the else-branch is the second body child, found here. Its own type
// is a statement kind rather than the vpiElseStmt relation tag, so the generic
// walk cannot serve it; null when the statement has no else branch. Backs the
// public vpi_handle(vpiElseStmt, if-else) dispatch.
VpiHandle VpiIfElseStmt(VpiHandle if_stmt);

// §37.74 For: the controlling condition expression a for statement reaches
// through vpiCondition. The condition's own type is an expression kind rather
// than the vpiCondition relation tag, so it is found as the for statement's
// first expression child; the initialization, increment, and body statements
// are statement-edge children and are skipped. Null when none is attached.
// Backs the public vpi_handle(vpiCondition, for) dispatch.
VpiHandle VpiForConditionExpr(VpiHandle for_stmt);

// §37.12 detail 1: whether an object kind is a block item declaration - a
// variable declaration or a type declaration. These are the declarations whose
// presence makes an unnamed begin or unnamed fork a scope.
bool VpiIsBlockItemDeclType(int type);

// §37.12 details 1 and 2: whether a begin/fork/for block object is a scope. A
// named begin or named fork is always a scope. An unnamed begin or unnamed fork
// is a scope if and only if it directly contains a block item declaration
// (VpiIsBlockItemDeclType). A for statement is a scope if and only if its
// vpiLocalVarDecls property is true. Any other object is not classified here.
bool VpiBlockScopeIsScope(VpiHandle block);

// §37.12 details 2 and 3: whether an object kind is a loop control variable -
// the variable a for or foreach statement declares as its index. The variable
// kinds qualify; a type or parameter declaration does not. Used to route a loop
// control variable's vpiScope to its enclosing loop statement.
bool VpiIsLoopControlVarType(int type);

// §37.12 detail 6: whether `join_type` is a legal value of the vpiJoinType
// property - one of vpiJoin, vpiJoinNone, or vpiJoinAny. Scopes
// vpi_get(vpiJoinType), which reports the stored value only when it is one of
// the three.
bool VpiIsJoinType(int join_type);

// §37.12 detail 5: whether an object kind is a task or a function - the "task
// func" node of the scope diagram whose body is reached through vpiStmt.
bool VpiIsTaskFuncType(int type);

// §37.12 detail 5: the body statement of a task or function, reached through
// vpiStmt. A task or function with no statements reports null; with exactly one
// statement it reports that statement; with more than one the statements are
// grouped under an unnamed begin and that begin is reported. In every nonzero
// case the body is the task/func's single statement child, so this returns the
// first statement child, or null when the body is empty. Backs the public
// vpi_handle(vpiStmt, task_func) dispatch.
VpiHandle VpiTaskFuncStmt(VpiHandle task_func);

// §37.59 detail 1: the operand order of a vpiMultiConcatOp operation. The first
// operand is the multiplier expression; the remaining operands are the
// expressions within the concatenation, in source order.
std::vector<VpiHandle> VpiMultiConcatOperands(
    VpiHandle multiplier, const std::vector<VpiHandle>& concat_exprs);

// §37.59 detail 7: the operand order of a vpiMultiAssignmentPatternOp
// operation. As with multiconcat, the first operand is the multiplier
// expression and the remaining operands are the expressions within the
// assignment pattern.
std::vector<VpiHandle> VpiMultiAssignmentPatternOperands(
    VpiHandle multiplier, const std::vector<VpiHandle>& pattern_exprs);

// §37.59 detail 3: a cast operation (vpiOpType == vpiCastOp) is modeled as a
// unary operation whose sole operand is the expression being cast; the type
// cast to is reached through the one-to-one typespec relation (detail 5). The
// operand list is therefore exactly that single argument.
std::vector<VpiHandle> VpiCastOpOperands(VpiHandle cast_expr);

// §37.59 detail 6: an assignment pattern (vpiAssignmentPatternOp) resolves its
// keyed entries (member, type, index, or default keys) to positional notation
// before vpiOperand iterates it. One entry assigns a value to a target
// position.
struct VpiAssignmentPatternEntry {
  int position = 0;  // 0-based target position this entry fills
  VpiHandle value = nullptr;
};

// §37.59 detail 6: build the positional operand list of an assignment pattern.
// `slots` is the number of target positions (struct members or array elements);
// each positioned entry fills its position, and any position left unassigned
// takes `default_value`. The result is the value of position 0..slots-1 in
// order. Values stay opaque handles, so a nested assignment-pattern operand is
// preserved as a single handle - nesting is not flattened.
std::vector<VpiHandle> VpiAssignmentPatternPositionalOperands(
    int slots, const std::vector<VpiAssignmentPatternEntry>& positioned,
    VpiHandle default_value);

// §37.59 detail 5: the one-to-one typespec relation of an expression is always
// available for a cast operation, for a simple expression, and for an
// assignment- pattern operation
// (vpiAssignmentPatternOp/vpiMultiAssignmentPatternOp) whose curly braces are
// prefixed by a data type name. For every other expression it is implementation
// dependent, so the guarantee does not hold. Returns whether a typespec is
// guaranteed to be available.
bool VpiTypespecAlwaysAvailable(int op_type, bool is_simple_expr,
                                bool assignment_pattern_has_type_prefix);

// §37.59 detail 9: vpiConstantSelect of a part-select or indexed part-select.
// It is TRUE only when vpiConstantSelect is TRUE for the parent, the parent is
// a packed or unpacked array with static bounds, and every range expression of
// the (indexed) part-select is an elaboration-time constant; otherwise FALSE.
struct VpiPartSelectConstantSelectQuery {
  bool parent_constant_select = false;
  bool parent_array_has_static_bounds = false;
  bool all_range_exprs_constant = false;
};
bool VpiPartSelectConstantSelect(const VpiPartSelectConstantSelectQuery& query);

// §37.59 detail 10: the vpiParent of a part-select or indexed part-select is
// the expression formed by removing the part-select range - the expression with
// its trailing bracketed selection dropped (Table 37-1). Given the decompiled
// select expression, returns the parent's decompiled form.
std::string VpiPartSelectParentExpr(std::string_view select_expr);

// §37.59 detail 2: vpiDecompile renders an expression as a functionally
// equivalent string with each operand and operator separated by a single space.
// Joins the pieces with exactly one space, skipping empty pieces so no double
// space appears.
std::string VpiDecompileJoin(const std::vector<std::string>& pieces);

// §37.59 detail 2: parentheses are added to a decompiled subexpression only to
// preserve precedence and introduce no white space - none inside the
// parentheses and none around them. Wraps `inner` accordingly.
std::string VpiDecompileParenthesize(std::string_view inner);

}  // namespace delta
