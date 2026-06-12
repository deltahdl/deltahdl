#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"

namespace delta {

class SimContext;
class Scheduler;
struct Net;
struct Variable;

constexpr int kVpiModule = 32;
constexpr int kVpiNet = 36;
constexpr int kVpiReg = 48;
constexpr int kVpiPort = 44;
constexpr int kVpiParameter = 41;
constexpr int kVpiCallback = 107;

// §38.13: a time queue object stands in for the simulator's pending-event
// queue. vpi_get_time() treats it specially, reporting the scheduled time of
// the next future event rather than the current simulation time.
constexpr int kVpiTimeQueue = 64;

constexpr int kVpiBinStrVal = 1;
constexpr int kVpiOctStrVal = 2;
constexpr int kVpiHexStrVal = 3;
constexpr int kVpiScalarVal = 4;
constexpr int kVpiIntVal = 5;
constexpr int kVpiRealVal = 6;
constexpr int kVpiStringVal = 7;
constexpr int kVpiTimeVal = 8;
constexpr int kVpiVectorVal = 9;
constexpr int kVpiStrengthVal = 10;
constexpr int kVpiObjTypeVal = 12;

constexpr int kVpiSimTime = 1;
constexpr int kVpiScaledRealTime = 2;

constexpr int kCbValueChange = 1;
constexpr int kCbReadWriteSynch = 2;
constexpr int kCbEndOfSimulation = 3;
constexpr int kCbStmt = 4;
constexpr int kCbAtStartOfSimTime = 5;
constexpr int kCbReadOnlySynch = 6;

constexpr int kCbAfterDelay = 7;
constexpr int kCbNextSimTime = 8;
constexpr int kCbNBASynch = 9;
constexpr int kCbAtEndOfSimTime = 10;

// §38.36.3: simulator action callbacks name reasons that every VPI-compliant
// tool provides (kCbEndOfSimulation above is also an action reason); simulator
// feature callbacks name optional, tool-specific reasons such as save, restart,
// reset, and interactive-mode transitions. They are registered through the same
// vpi_register_cb() path as every other callback reason.
constexpr int kCbEndOfCompile = 11;
constexpr int kCbStartOfSimulation = 12;
constexpr int kCbError = 13;
constexpr int kCbPLIError = 14;
constexpr int kCbTchkViolation = 15;
constexpr int kCbSignal = 16;
constexpr int kCbStartOfSave = 17;
constexpr int kCbEndOfSave = 18;
constexpr int kCbStartOfRestart = 19;
constexpr int kCbEndOfRestart = 20;
constexpr int kCbStartOfReset = 21;
constexpr int kCbEndOfReset = 22;
constexpr int kCbEnterInteractive = 23;
constexpr int kCbExitInteractive = 24;
constexpr int kCbInteractiveScopeChange = 25;
constexpr int kCbUnresolvedSystf = 26;

constexpr int kVpiType = 1;
constexpr int kVpiName = 2;
constexpr int kVpiFullName = 3;
constexpr int kVpiSize = 4;
constexpr int kVpiDirection = 5;
constexpr int kVpiDefName = 6;

// §37.3.7: vpiAutomatic is the standard Boolean lifetime selector (the same
// value 50 already used elsewhere in this header). It is repeated here as a
// kVpi* constant so the Get() switch can read an object's declared lifetime in
// the same idiom as the other property selectors.
constexpr int kVpiAutomatic = 50;

// §37.3.7: vpiAllocScheme is the enumeration property naming how an object's
// memory was obtained. 731 is the lowest selector value not yet claimed by any
// other property/object/callback constant in this module.
constexpr int kVpiAllocScheme = 731;

// §37.3.7: the three (and only three) allocation schemes vpi_get(vpiAllocScheme)
// may return. These live in the property-RETURN-value namespace, distinct from
// the selector numbers above, so small contiguous ints are unambiguous.
//   kVpiAutomaticScheme -> object lives with a frame or thread
//   kVpiDynamicScheme   -> object was allocated in dynamic memory (e.g. a class)
//   kVpiOtherScheme     -> the mandated default for every other object
constexpr int kVpiAutomaticScheme = 1;
constexpr int kVpiDynamicScheme = 2;
constexpr int kVpiOtherScheme = 3;

constexpr int kVpiLibrary = 67;
constexpr int kVpiConfig = 70;
constexpr int kVpiCell = 71;

constexpr int kVpiInput = 1;
constexpr int kVpiOutput = 2;
constexpr int kVpiInout = 3;

constexpr int kVpiNoDelay = 1;
constexpr int kVpiInertialDelay = 2;
constexpr int kVpiTransportDelay = 3;
constexpr int kVpiPureTransportDelay = 4;

constexpr int kVpiFinish = 66;
constexpr int kVpiStop = 67;
// §38.36.3: a reset can be requested indirectly through vpi_control(vpiReset).
constexpr int kVpiReset = 68;
// §38.4: vpi_control(vpiSetInteractiveScope, handle) immediately retargets the
// tool's interactive scope to the supplied vpiScope object.
constexpr int kVpiSetInteractiveScope = 69;

constexpr int kVpi0 = 0;
constexpr int kVpi1 = 1;
constexpr int kVpiX = 2;
constexpr int kVpiZ = 3;

// §38.2 Table 38-1: the vpi_chk_error() severity levels, ordered from lowest
// (vpiNotice) to highest (vpiInternal). The values increase with severity, so
// vpiSystem outranks vpiError and vpiInternal outranks them all.
constexpr int kVpiNotice = 1;
constexpr int kVpiWarning = 2;
constexpr int kVpiError = 3;
constexpr int kVpiSystem = 4;
constexpr int kVpiInternal = 5;

// §38.10: one delay element carried by a delay-bearing object (a primitive, a
// module path, a timing check, or an intermodule path). `delay` is the plain
// value reported when min:typ:max is not requested; the min/typ/max triples
// give the spread that mtm_flag asks for; reject/error (and their triples)
// carry the pulse-control limits that pulsere_flag asks for. vpi_get_delays()
// reads these and lays them out into the caller's array per Table 38-2.
struct VpiDelayInfo {
  double delay = 0.0;
  double min_delay = 0.0, typ_delay = 0.0, max_delay = 0.0;
  double reject = 0.0;
  double min_reject = 0.0, typ_reject = 0.0, max_reject = 0.0;
  double error = 0.0;
  double min_error = 0.0, typ_error = 0.0, max_error = 0.0;
};

struct VpiObject {
  int type = 0;
  std::string_view name;
  std::string full_name;
  Variable* var = nullptr;
  Net* net = nullptr;
  VpiObject* parent = nullptr;
  int direction = 0;
  int size = 0;
  int index = 0;

  // §6.9.2: the advisory accessibility keyword a vector net was declared with.
  // At most one is set. They drive how the PLI reports the net's expansion
  // through vpi_get(vpiExplicitScalared/vpiExplicitVectored/vpiExpanded): a
  // scalared net is always reported expanded; a vectored net is reported
  // unexpanded.
  bool is_vectored = false;
  bool is_scalared = false;

  // §37.3.7: declared lifetime. False means the object is static; true means it
  // is non-static (an automatic variable or a dynamic object). Static is the
  // default.
  bool automatic = false;

  // §37.3.7: how this object's storage was obtained. Defaulting to
  // kVpiOtherScheme directly encodes the rule that every object not allocated
  // with a frame/thread or in dynamic memory reports vpiOtherScheme.
  int alloc_scheme = kVpiOtherScheme;

  // §37.3.6: whether this object represents protected code (sealed in a
  // decryption envelope). Reported by the vpiIsProtected property. Unless
  // otherwise specified, accessing a protected object's properties is an error;
  // vpiType and vpiIsProtected are the permitted exceptions.
  bool is_protected = false;

  // §38.12: whether this callback object stands in for a user-defined system
  // task or system function. When true, `index` selects the registration
  // record vpi_get_systf_info() reports; this separates a system task/function
  // callback from a simulation callback, which is also a vpiCallback object.
  bool is_systf = false;

  // §38.34: whether a vpiSchedEvent handle still names an event sitting in the
  // event queue. vpi_put_value() with vpiReturnEvent hands back such a handle
  // marked scheduled; vpi_get(vpiScheduled) reports this flag, and
  // vpi_put_value() with vpiCancelEvent clears it when the event is removed.
  bool scheduled = false;

  // §37.10 detail 6: items that vpi_handle_by_name() must not be able to reach.
  // An imported item is brought into scope by an import declaration; a
  // compilation-unit object lives directly in the $unit compilation-unit scope.
  bool imported = false;
  bool in_compilation_unit = false;

  // §37.16 detail 9: whether a net was created by implicit declaration (a net
  // referenced without an explicit declaration). Reported by vpiImplicitDecl;
  // an implicit net's vpiLineNo is 0 and its vpiFile names where the net was
  // first referenced (carried in `file`).
  bool implicit_decl = false;

  // §37.10 detail 7: the time precision an instance was elaborated with. Only
  // meaningful on module objects; the design-wide query reads it across every
  // module to find the smallest precision.
  int time_precision = 0;

  // §38.13: the object's time unit, as a base-ten exponent of one second (e.g.
  // -9 for 1 ns, -12 for 1 ps). vpi_get_time() scales a scaled-real result to
  // this unit - the "timescale of the object". Zero leaves the scaled value
  // expressed in the simulation time unit (no scaling).
  int time_unit = 0;

  std::string library_name;
  std::string cell_name;
  std::string config_name;

  // §37.30 detail 1: the definition name an interface typespec reports through
  // vpi_get_str(vpiDefName) - the modport identifier when the typespec
  // represents a modport, the interface declaration's identifier when it
  // represents an interface. Distinct from `name`, which carries the typespec's
  // vpiName (the typedef name); empty when unset.
  std::string def_name;

  // §37.54 (D2): the operation type an operation object reports through
  // vpi_get(vpiOpType). For a sequence expression's operation this is one of the
  // sequence operators (see VpiIsSequenceExprOpType); zero when unset.
  int op_type = 0;

  // §37.59: the constant type a constant object reports through
  // vpi_get(vpiConstType). vpiUnboundedConst names the $ value used in assertion
  // ranges (detail 4). Zero when unset.
  int const_type = 0;

  // §37.59: the index-part-select type an indexed part-select reports through
  // vpi_get(vpiIndexedPartSelectType) - whether the selection ascends (+:) or
  // descends (-:). Zero when unset.
  int indexed_part_select_type = 0;

  // §37.52 detail 3: whether an operation reports the strong version of its
  // operator through vpi_get(vpiOpStrong). Meaningful only for the operators
  // VpiIsOpStrongValidOp accepts (and for sequence expressions); false otherwise.
  bool op_strong = false;

  // §37.50: whether a cover covers a sequence rather than a property, reported
  // through vpi_get(vpiIsCoverSequence). Meaningful only for a cover; false
  // otherwise.
  bool cover_sequence = false;

  // §37.50 (detail 1): whether the concurrent assertion's clocking event was
  // inferred from context rather than written explicitly, reported through
  // vpi_get(vpiIsClockInferred). The event reached through vpiClockingEvent is
  // the actual event either way; this flag only records which form produced it.
  bool clock_inferred = false;

  // §37.43/§37.44: whether a frame or a thread is the active one, reported
  // through vpi_get(vpiActive). The object that currently holds execution is
  // active; an inactive one is suspended or otherwise not running. There is at
  // most one active frame at a time in a given thread (§37.43 detail 4). False
  // by default.
  bool active = false;

  // §37.49: the source span an assertion object occupies. start/column/end are
  // reported through vpi_get(vpiStartLine/vpiColumn/vpiEndLine/vpiEndColumn) and
  // the file through vpi_get_str(vpiFile); the assertion name reuses `name`.
  std::string file;
  int start_line = 0;
  int column = 0;
  int end_line = 0;
  int end_column = 0;

  // §38.10: the delays this object carries, in the order they occur in the
  // SystemVerilog description. vpi_get_delays() reports them in this order, so
  // da[0] is the first source delay, da[1] the second, and so on. Empty for an
  // object that bears no delays.
  std::vector<VpiDelayInfo> delays;

  // §37.14 / §37.15: a port (or a ref obj) carries two designated connections.
  // vpiHighConn reaches the hierarchically higher connection (closer to the top
  // module); vpiLowConn reaches the lower one. A null pointer is the natural
  // encoding of "no such connection", which §37.14 detail 10 mandates as NULL
  // for a null port (lowConn) or an unconnected instance (highConn).
  VpiObject* high_conn = nullptr;
  VpiObject* low_conn = nullptr;

  // §37.15 detail 3: the actual instantiated object a ref obj is bound to,
  // reported through the vpiActual relation. NULL when the ref obj is not bound
  // to an actual at the time of the query.
  VpiObject* actual = nullptr;

  // §37.14 detail 1: a port's type, one of vpiPort, vpiInterfacePort, or
  // vpiModportPort, reported through vpi_get(vpiPortType). It is derived from the
  // formal, not the actual. Zero when unset.
  int port_type = 0;

  // §37.14 detail 8: whether a port was given an explicit name in the port list,
  // reported through vpi_get(vpiExplicitName).
  bool explicit_name = false;

  // §37.14 detail 10/11: whether a port is a null port (e.g. "module M();").
  // Its vpiLowConn is NULL and its vpiSize is 0.
  bool null_port = false;

  // §37.15 detail 5: whether a ref obj refers to a generic interface. Only
  // meaningful when the ref obj refers to an interface; reported through
  // vpi_get(vpiGeneric).
  bool generic_interface = false;

  // §37.30: whether an interface typespec represents a modport rather than an
  // interface, reported through vpi_get(vpiIsModPort). It also selects how
  // vpiDefName and vpiParent are interpreted (details 1 and 2). False (an
  // interface, not a modport) by default.
  bool is_modport = false;

  std::vector<VpiObject*> children;
  size_t scan_index = 0;

  // §38.23: for an iterator object (type vpiIterator), the reference object the
  // iteration was created over. It is reported back through the vpiUse relation,
  // so vpi_handle(vpiUse, iterator) recovers the object the iterator walks.
  VpiObject* iter_ref = nullptr;
};

using VpiHandle = VpiObject*;

// §37.3.7: the categories an allocator can place an object into, used to derive
// its vpiAllocScheme. Keeping this separate from the scheme return values lets
// callers describe an allocation in intent ("this came from a frame") and have
// the mapping to the reported scheme live in one place.
enum class VpiAllocKind {
  kFrameOrThread,  // allocated with a frame or thread -> Automatic scheme
  kDynamic,        // allocated in dynamic memory (class object) -> Dynamic
  kOther,          // anything else -> the mandated Other default
};

// §37.3.7: map an allocation category to the vpiAllocScheme value that
// vpi_get(vpiAllocScheme) must report. Unrecognized/other allocations fall
// through to kVpiOtherScheme, satisfying the "all other objects" default.
int VpiAllocSchemeFor(VpiAllocKind kind);

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

// §37.49: the assertion class groups the concurrent assert/assume/cover/restrict
// kinds, the immediate assert/assume/cover kinds, and sequence and property
// instances. An object is an assertion exactly when its type is one of these.
bool VpiIsAssertionType(int type);

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

// §37.50: the property a concurrent assertion traverses to through vpiProperty -
// its first property-instance/specification child; null for a null handle or an
// assertion with no property attached.
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
// vpiStmt - its first statement child; null when none is attached (for example a
// restrict, which has no pass action statement).
VpiHandle VpiConcurrentAssertionStmt(VpiHandle assertion);

// §37.50: the else (fail) action statement a concurrent assertion traverses to
// through vpiElseStmt - its first else-statement child; null when none is
// attached (a cover or restrict has none).
VpiHandle VpiConcurrentAssertionElseStmt(VpiHandle assertion);

// §37.50 (detail 2): whether a concurrent assertion kind is simulated and so
// generates run-time information. Every kind is, except restrict, which is not
// simulated and hence generates no run-time information.
bool VpiConcurrentAssertionIsSimulated(int type);

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

// §37.54 detail 1: a sequence formal as seen by the argument iteration. A formal
// may carry a default value (null when it has none) that is used as the argument
// when an instantiation does not provide one.
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
// an operation, a multiclock sequence expression, a property instance, a clocked
// property, and a case property. (A sequence expression is also a property
// expression; classifying the sequence-expr kinds is the sequence-expr class's
// concern.) The class selector itself is not one of these member kinds.
bool VpiIsPropertyExprType(int type);

// §37.52 detail 2: the property operators a property expr's operation may report
// through vpi_get(vpiOpType). Every other operator value is not a property
// operator.
bool VpiIsPropertyExprOpType(int op);

// §37.52 detail 2 (vpiNexttimeOp exception): the operands of a nexttime
// operation in the order vpiOperand presents them - the property, then the
// constant. The constant is reported only when it differs from 1.
std::vector<VpiHandle> VpiNexttimeOperands(VpiHandle property, VpiHandle constant,
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
// condition members, each of which branches to the item's property statement, in
// order. A case property item's property statement (the diagram's case property
// item -> property expr edge) is excluded. The default case item has no
// condition expression, so it groups none (detail 5).
std::vector<VpiHandle> VpiCaseItemConditions(VpiHandle case_item);

// §37.52: the kinds the property-spec/property-expr disable-condition relation
// may reach - a bare expression or a distribution. (A property instance's
// disable condition reaches only an expression; see §37.51.)
bool VpiIsDisableConditionType(int type);

// §37.52: the clocking event a property spec or clocked property traverses to
// through vpiClockingEvent (the diagram's -> expr edge), modeled as the object's
// event-control child; null when none is present. §37.56's clocked seq shares
// this relation (its own vpiClockingEvent -> expr edge has the same shape).
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
// variable argument reports vpiInput; every other formal reports vpiNoDirection.
int VpiPropFormalDirection(bool is_local_variable_argument);

// §37.51 detail 3: the typespec of a property formal (its vpiTypespec child), or
// null when the formal is untyped.
VpiHandle VpiPropFormalTypespec(VpiHandle formal);

// §37.51 detail 4: the initialization expression of a property formal, reached
// through vpiExpr. The diagram draws this target as a named event or a property
// expression; null when the formal has no initialization expression.
VpiHandle VpiPropFormalInitExpr(VpiHandle formal);

// §37.51 detail 2: a property formal as seen by the property-instance argument
// iteration. A formal may carry a default value (null when none) that is used as
// the argument when an instantiation does not provide one.
struct VpiPropertyFormal {
  VpiHandle default_value = nullptr;
};

// §37.51 detail 2: the arguments the vpiArgument iteration returns for a property
// instance, in formal-declaration order so each argument corresponds to its
// formal. `provided` is parallel to `formals`; a null entry means the
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
// so this returns the multiclock sequence expression's vpiClockedSeq children in
// order, dropping anything else. A null handle yields none.
std::vector<VpiHandle> VpiMulticlockSequenceClockedSeqs(VpiHandle multiclock_seq);

// §37.56: the sequence expression a clocked seq clocks (the diagram's single
// tagless arrow, vpi_handle(vpiSequenceExpr, ...)). A clocked seq pairs one
// clocking event with one sequence expression, so this is the clocked seq's
// first sequence-expr-kind child (classified by VpiIsSequenceExprType); null for
// a null handle or a clocked seq with no sequence expression attached. The
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

// §37.53 detail 4: a seq formal decl's vpiDirection. A formal that is not a local
// variable argument has no direction (vpiNoDirection); a local variable argument
// reports its declared direction, one of vpiInput, vpiOutput, or vpiInout. (This
// is the sequence analog of §37.51's property formal, which only ever reports
// vpiInput.)
int VpiSeqFormalDirection(bool is_local_variable_argument, int local_direction);

// §37.53 detail 2: the typespec of a seq formal decl (its vpiTypespec child), or
// null when the formal is untyped.
VpiHandle VpiSeqFormalTypespec(VpiHandle formal);

// §37.53 detail 3: the initialization expression of a seq formal decl, reached
// through vpiExpr. The diagram draws its target as a named event or a sequence
// expression (§37.54); null when the formal has no initialization expression.
VpiHandle VpiSeqFormalInitExpr(VpiHandle formal);

// ===========================================================================
// §37.59 Expressions. The VPI object model for an expression. The expr class
// groups operations, constants, part-selects and indexed part-selects, the
// function/method-function/system-function calls and let expressions, and a
// simple expression (a reference). Every expression carries the vpiDecompile,
// vpiSize and value properties; an operation carries vpiOpType, a constant
// vpiConstType, and an indexed part-select vpiIndexedPartSelectType (all applied
// by VpiContext::Get). The helpers below carry the subclause's normative details.
// ===========================================================================

// §37.59: the kinds the expr class groups in the data model diagram - an
// operation, a constant, a part-select or indexed part-select, a func/method-func/
// sys-func call, a let expression, and a reference (the concrete simple
// expression). Used to scope detail 8's protected-object carve-out (vpiSize stays
// accessible on a protected expression) and to classify diagram members.
bool VpiIsExprType(int type);

// §37.60: the statement kinds the atomic stmt class groups in the object model
// diagram - the procedural control statements (if, if-else, while, repeat, the
// waits, case, for, the timing controls, the event statement, the assignments,
// deassign, the disables, the tf calls, forever, force, release, do-while, the
// expect/foreach/return statements, break, continue, the immediate assertions,
// and the null statement). Used to scope detail 1, which gives an atomic
// statement a single label edge: vpiName reports its label, or NULL when none.
bool VpiIsAtomicStmtType(int type);

// §37.64 Assignment detail 1: the vpiOpType an assignment object reports. A normal
// assignment - blocking "=" or nonblocking "<=" - reports vpiAssignmentOp. An
// assignment written with an assignment operator instead reports the operator
// combined with the assignment, following 11.4.1: "+=" reports vpiAddOp, "-="
// vpiSubOp, "<<<=" vpiArithLShiftOp, and so on. `assign_operator` is the source
// spelling of the operator ("=", "<=", "+=", ...). Any spelling that is not one of
// the assignment operators is treated as a normal assignment (vpiAssignmentOp).
int VpiAssignmentOpType(std::string_view assign_operator);

// §37.59 detail 1: the operand order of a vpiMultiConcatOp operation. The first
// operand is the multiplier expression; the remaining operands are the
// expressions within the concatenation, in source order.
std::vector<VpiHandle> VpiMultiConcatOperands(
    VpiHandle multiplier, const std::vector<VpiHandle>& concat_exprs);

// §37.59 detail 7: the operand order of a vpiMultiAssignmentPatternOp operation.
// As with multiconcat, the first operand is the multiplier expression and the
// remaining operands are the expressions within the assignment pattern.
std::vector<VpiHandle> VpiMultiAssignmentPatternOperands(
    VpiHandle multiplier, const std::vector<VpiHandle>& pattern_exprs);

// §37.59 detail 3: a cast operation (vpiOpType == vpiCastOp) is modeled as a
// unary operation whose sole operand is the expression being cast; the type cast
// to is reached through the one-to-one typespec relation (detail 5). The operand
// list is therefore exactly that single argument.
std::vector<VpiHandle> VpiCastOpOperands(VpiHandle cast_expr);

// §37.59 detail 6: an assignment pattern (vpiAssignmentPatternOp) resolves its
// keyed entries (member, type, index, or default keys) to positional notation
// before vpiOperand iterates it. One entry assigns a value to a target position.
struct VpiAssignmentPatternEntry {
  int position = 0;          // 0-based target position this entry fills
  VpiHandle value = nullptr;
};

// §37.59 detail 6: build the positional operand list of an assignment pattern.
// `slots` is the number of target positions (struct members or array elements);
// each positioned entry fills its position, and any position left unassigned takes
// `default_value`. The result is the value of position 0..slots-1 in order. Values
// stay opaque handles, so a nested assignment-pattern operand is preserved as a
// single handle - nesting is not flattened.
std::vector<VpiHandle> VpiAssignmentPatternPositionalOperands(
    int slots, const std::vector<VpiAssignmentPatternEntry>& positioned,
    VpiHandle default_value);

// §37.59 detail 5: the one-to-one typespec relation of an expression is always
// available for a cast operation, for a simple expression, and for an assignment-
// pattern operation (vpiAssignmentPatternOp/vpiMultiAssignmentPatternOp) whose
// curly braces are prefixed by a data type name. For every other expression it is
// implementation dependent, so the guarantee does not hold. Returns whether a
// typespec is guaranteed to be available.
bool VpiTypespecAlwaysAvailable(int op_type, bool is_simple_expr,
                                bool assignment_pattern_has_type_prefix);

// §37.59 detail 9: vpiConstantSelect of a part-select or indexed part-select. It
// is TRUE only when vpiConstantSelect is TRUE for the parent, the parent is a
// packed or unpacked array with static bounds, and every range expression of the
// (indexed) part-select is an elaboration-time constant; otherwise FALSE.
struct VpiPartSelectConstantSelectQuery {
  bool parent_constant_select = false;
  bool parent_array_has_static_bounds = false;
  bool all_range_exprs_constant = false;
};
bool VpiPartSelectConstantSelect(const VpiPartSelectConstantSelectQuery& query);

// §37.59 detail 10: the vpiParent of a part-select or indexed part-select is the
// expression formed by removing the part-select range - the expression with its
// trailing bracketed selection dropped (Table 37-1). Given the decompiled select
// expression, returns the parent's decompiled form.
std::string VpiPartSelectParentExpr(std::string_view select_expr);

// §37.59 detail 2: vpiDecompile renders an expression as a functionally equivalent
// string with each operand and operator separated by a single space. Joins the
// pieces with exactly one space, skipping empty pieces so no double space appears.
std::string VpiDecompileJoin(const std::vector<std::string>& pieces);

// §37.59 detail 2: parentheses are added to a decompiled subexpression only to
// preserve precedence and introduce no white space - none inside the parentheses
// and none around them. Wraps `inner` accordingly.
std::string VpiDecompileParenthesize(std::string_view inner);

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
// was activated, reached up the parent chain when that parent is itself a frame.
// Null for a null handle, a root frame with no parent, or a non-frame parent.
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

// §37.44 (vpiParent -> thread): the thread that spawned this one, reached up the
// parent chain. Returns the thread's parent when that parent is itself a thread;
// null for a null handle, a root thread with no parent, or a parent that is not
// a thread.
VpiHandle VpiThreadParent(VpiHandle thread);

// §37.44 (vpiOrigin -> stmt): the statement a thread originated from, modeled as
// the thread's first statement child. Null for a null handle or a thread with no
// origin statement attached.
VpiHandle VpiThreadOrigin(VpiHandle thread);

// §37.44 (frame -- thread / detail 1): the active frame of a thread. As a thread
// descends a call chain of tasks and functions a new frame is activated for each
// one entered, and at most one is active at a time (§37.43); this returns that
// frame, modeled as the thread's first frame child. Null for a null handle or a
// thread with no frame attached.
VpiHandle VpiThreadFrame(VpiHandle thread);

// §37.44 (thread one-to-many thread): the threads spawned by this thread, as the
// iteration over its thread children yields them, in order. A null handle yields
// none.
std::vector<VpiHandle> VpiThreadThreads(VpiHandle thread);

// ===========================================================================
// §37.22 Object range. A range object carries the bounds of one array
// dimension. §37.17's range relations (details 4 and 6) are woven onto these
// helpers, so a range that one subclause calls "empty" behaves identically in
// the other.
// ===========================================================================

// §37.22 detail 1: a range object's contents. An empty range has no elements; it
// stands in for an associative-array dimension, an empty dynamic array or queue,
// and any range obtained from a typespec for a dynamic-array, queue, or
// associative dimension. A non-empty range carries the bound expressions reached
// through vpiLeftRange/vpiRightRange and an element count.
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
// vpiExpr (modeled as the variable's first child). Null when the variable has no
// initialization expression.
VpiHandle VpiVariableInitExpr(VpiHandle var);

// §37.17 detail 14: whether the cbSizeChange callback is applicable to a
// variable. It applies only to dynamic arrays, associative arrays, queues, and
// string variables; array_type is the variable's vpiArrayType (0 when not an
// array). The detail's firing-order and new-size-value semantics need a
// size-change callback engine the simulator does not have, so only applicability
// is realized here.
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

// §37.17 detail 6: vpiRightRange of a variable, the mirror of VpiVariableLeftRange.
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

// §37.17 details 9 and 10: the inputs vpiSize reads for a variable or var select.
struct VpiVariableSizeQuery {
  int var_type = 0;
  bool packed = false;          // struct/union var: packed vs unpacked
  int bit_width = 0;            // integer-typed/packed/enum var, packed var select
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

// §37.17 detail 11: whether a variable kind has a value property. Array, class,
// and virtual-interface variables do not; an unpacked struct or union variable
// (vpiVector FALSE) does not; every other variable kind does.
bool VpiVariableHasValueProperty(int var_type, bool vpi_vector);

// §37.17 detail 12: the vpiBit iterator applies only to logic, bit, packed
// struct, packed union, and packed array variables.
bool VpiBitIteratorApplies(int var_type, bool packed);

// §37.17 details 15 and 22: vpiRandType is one of vpiRand, vpiRandC, vpiNotRand.
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
// dimension) and a var bit are scalars; an enum var defers to its base typespec;
// an array var defers to an element; every other variable is not a scalar.
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

// §37.17 detail 25: vpiFullName for a class data member. A non-static member has
// none (the empty string marks its absence); a static member's full name is the
// hierarchical path written through its "class defn", e.g. "top.Packet::Id".
std::string VpiClassMemberFullName(bool is_static, std::string_view scope_path,
                                   std::string_view class_defn,
                                   std::string_view member);

// §37.17 detail 26: a candidate vpiParent prefix object, in prefix order
// (rightmost/innermost first). A prefix qualifies when it is a struct/union/class
// variable, a struct/union member or class data member, or the largest
// containing packed or unpacked array object; otherwise its handle is null.
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
  bool has_parent = false;                    // vpiParent != NULL
  bool all_indices_constant = false;          // every index is elaboration-constant
  bool all_elements_static_members = false;   // struct/union members or packed/
                                              // unpacked array elements with
                                              // static bounds
};

// §37.17 detail 27: vpiConstantSelect. TRUE when the variable has static lifetime
// and no parent, or when every index expression is an elaboration-time constant
// and every selected element is a struct/union member or a packed/unpacked array
// element with static bounds; FALSE otherwise.
bool VpiConstantSelect(const VpiConstantSelectQuery& query);

// §37.17 detail 28: the components of a member variable's name. The struct/union/
// class-var prefixes run outermost first; the object's own index/slice (if any)
// is carried separately so it can be appended to all three name forms.
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
// index/slice) without the top-level scope, so it resolves for any non-top-level
// scope context.
std::string VpiVariableDecompile(const VpiVariableNameParts& parts);

// §37.17 detail 28: vpiFullName - the top-level scope prefixed to the decompile
// form.
std::string VpiVariableFullName(const VpiVariableNameParts& parts);

// ===========================================================================
// §37.25 Typespec. The VPI object model for a type specification. Each helper
// applies one of the clause's numbered "Details"; the figure's range relations
// route through §37.22 and a member's expr role reuses §37.59's expr class. The
// figure attributes that carry no numbered Detail (vpiTagged/vpiSoft/vpiPacked/
// vpiVector/vpiArrayType/vpiRandType) are defined by §37.26 and §37.17, not here.
// ===========================================================================

// §37.25: the object-type codes the data model groups under the typespec class -
// every "... typespec" node of Figure 37.25, plus an unresolved type parameter,
// which acts as a typespec (detail 11). Used to tell a member's typespec child
// from its default-value expr child.
bool VpiIsTypespecType(int type);

// §37.25 detail 1: vpiName of a typespec. A typespec that denotes a user-defined
// typedef reports that typedef's name (which may be the empty string for a field
// defined inline, detail 5); a class typespec always reports the class name;
// every SystemVerilog built-in type reports NULL.
const char* VpiTypespecName(int ts_type, bool denotes_user_typedef,
                            const char* typedef_name, const char* class_name);

// §37.25 detail 1: vpiTypedefAlias of a typespec. A typespec whose typedef
// creates an alias of another typedef hands back a handle to the aliased typedef;
// a typespec that is not such an alias reports NULL.
VpiHandle VpiTypespecTypedefAlias(bool is_alias, VpiHandle aliased_typedef);

// §37.25 detail 2: vpiIndexTypespec of a typespec. The relation exists only on an
// associative-array typespec, where it yields the type used as the array key; a
// wildcard index type (see 7.8.1) yields NULL, and so does any typespec that is
// not an associative array.
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

// §37.25 detail 4: vpiName of a typespec member is the member's own name, not the
// name of the member's typespec.
const char* VpiTypespecMemberName(VpiHandle member);

// §37.25 detail 7: the expr of a typespec member is the explicit default value of
// the corresponding member of an unpacked structure (see 7.2), reached as the
// member's expr child; a member with no default reports NULL.
VpiHandle VpiTypespecMemberDefaultExpr(VpiHandle member);

// §37.25 detail 8: vpi_handle(vpiElemTypespec, typespec) unwinds one array
// dimension at a time. A typespec that still has at least one range hands back
// the element typespec with its leftmost range removed; a typespec with no ranges
// present yields NULL.
VpiHandle VpiTypespecElemTypespec(bool has_ranges, VpiHandle element_typespec);

// §37.25 detail 10 (woven with §37.22): the ranges vpi_iterate(vpiRange,
// typespec) returns, one per dimension from leftmost to rightmost. For an array
// typespec these are the unpacked ranges; for a bit or logic typespec they are
// the packed ranges. A dynamic-array, queue, or associative dimension contributes
// an empty range.
std::vector<VpiRangeDesc> VpiTypespecRanges(
    const std::vector<VpiArrayDimension>& dims);

// §37.25 detail 9: vpiLeftRange of a typespec - the left bound of its leftmost
// dimension (the leftmost packed dimension of a logic/bit/packed-array typespec,
// the leftmost unpacked dimension of an array typespec). NULL when there is no
// dimension or that leftmost range is empty (§37.22).
VpiHandle VpiTypespecLeftRange(const std::vector<VpiArrayDimension>& dims);

// §37.25 detail 9: vpiRightRange of a typespec, the mirror of VpiTypespecLeftRange.
VpiHandle VpiTypespecRightRange(const std::vector<VpiArrayDimension>& dims);

// §37.25 detail 11: in a context where a type parameter has not been resolved,
// the type parameter itself acts as the typespec. Returns the resolved typespec
// when one exists, otherwise the type parameter handle itself.
VpiHandle VpiTypespecForTypeParameter(VpiHandle type_parameter,
                                      VpiHandle resolved_typespec);

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
// interface expr. A ref obj qualifies only when its vpiActual is an interface or
// a modport (a local declaration passed through a port); a constant only when
// its vpiConstType is vpiNullConst; an interface, modport, or virtual interface
// var always qualifies.
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

// §37.13 detail 4 (woven with §37.25): the ranges vpi_iterate(vpiRange, io_decl)
// returns are the same as for the io decl's corresponding typespec, so this
// defers to §37.25's typespec range helper.
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
// port's vpiHighConn/vpiLowConn connections are reached the same way a ref obj's
// are, and the lowConn of an interface port is itself a ref obj (§37.14 detail
// 5), so the connection helpers below serve both. The numbered "Details" that
// carry decision rules are realized as helpers; the diagram's structural
// relations are served by the generic Handle/Get machinery once the designated
// connection pointers are populated.
// ===========================================================================

// §37.14 detail 1: the three port types a port may report through
// vpi_get(vpiPortType). The value is determined by the formal, never the actual.
bool VpiIsValidPortType(int port_type);

// §37.14 detail 1: the port type derived from what the formal denotes - an
// interface formal yields vpiInterfacePort, a modport formal vpiModportPort, and
// any ordinary formal vpiPort. The actual a port connects to never changes this.
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
// TRUE when the port is not an interface port, or it is and its lowConn is a ref
// obj; FALSE when an interface port's lowConn is missing or some other kind.
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
const char* VpiPortName(bool explicitly_named, const char* explicit_name,
                        const char* inferred_name);

// §37.14 detail 11: vpiSize for a port. A null port reports 0; any other port
// reports its bit width.
int VpiPortSize(bool is_null_port, int port_width);

// §37.15 detail 5: vpiGeneric for a ref obj. TRUE when the ref obj refers to a
// generic interface, FALSE when it refers to a non-generic interface, and
// vpiUndefined for every other kind of ref obj.
int VpiRefObjGeneric(bool refers_to_interface, bool is_generic_interface);

// §37.15 detail 6: vpiDefName for a ref obj whose vpiActual is an interface or a
// modport returns that interface's definition name or the modport name. NULL for
// a ref obj whose actual is neither (or which is unbound).
const char* VpiRefObjDefName(VpiHandle ref_obj);

// §37.15 detail 7: the vpiTypespec relation returns NULL for a ref obj whose
// vpiActual is not a net, variable, or part select; otherwise it returns the ref
// obj's typespec child.
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

// §37.16 detail 2: vpiArrayMember is TRUE exactly when a net is an element of an
// array net, read from the net's vpiParent prefix. (The older vpiArray property
// is deprecated for the same role.)
bool VpiNetIsArrayMember(VpiHandle net);

// §37.16 detail 2: vpiPackedArrayMember is TRUE for a packed struct net, packed
// union net, enum net, or packed array net that is an element of a packed array
// net (its vpiParent prefix is a packed array net).
bool VpiNetIsPackedArrayMember(VpiHandle net);

// §37.16 detail 3: a net bit of a logic net or bit net is always reachable
// through vpiBit, regardless of whether the vector was expanded. True for a
// logic net or a bit net.
bool VpiNetBitIteratorApplies(int net_type);

// §37.16 detail 5: continuous assignments and primitive terminals (vpiContAssign
// and vpiPrimTerm) shall only be accessed from a scalar net or a bit-select.
bool VpiNetTerminalAccessAllowed(bool is_scalar_net_or_bit_select);

// §37.16 details 6 and 7: the granularity a vpiPorts or vpiPortInst iteration
// hands back for a given reference handle - either the individual port bits (or
// scalar ports) matching the reference, or a handle to the entire port.
enum class VpiPortGranularity {
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

// §37.16 detail 10: vpi_handle(vpiIndex, net_bit) returns the bit index of a net
// bit - its single innermost index.
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

// §37.16 detail 11: vpiDriver and vpiLocalDriver iterations are not supported for
// a net whose vpiNetType is vpiNettypeNetSelect.
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

// §37.16 detail 23: vpiConstantSelect for a net or net bit. TRUE when the object
// has no parent (vpiParent returns NULL), or when every index expression in the
// select is an elaboration-time constant and every selected element denotes a
// struct/union net member or a packed/unpacked array element with static bounds
// (see A.8.4); FALSE otherwise.
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
// bound of the leftmost packed dimension. NULL when the net has no dimensions or
// that leftmost range is empty.
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

// §37.16 detail 30: whether a net kind has a value property. Array nets, unpacked
// struct nets, unpacked union nets, and interconnect arrays do not; every other
// net does.
bool VpiNetHasValueProperty(int net_type, bool packed_struct_union);

// §37.16 detail 31: vpiParent of a net. Scanning the prefix objects rightmost to
// leftmost (the order given), the first qualifying prefix is returned - a
// struct/union net, a struct/union member net, or the largest containing packed
// or unpacked array net; NULL when none qualifies. Reuses §37.17's prefix
// descriptor, whose shape is shared between the two object models.
VpiHandle VpiNetParent(const std::vector<VpiParentPrefix>& prefixes);

// §37.16 detail 32: vpiElement iterates the subelements of a packed array net,
// one dimension at a time. True for a packed array net, false for any other net.
bool VpiNetElementIteratorApplies(int net_type);

// §37.16 detail 32: the subelements a vpiElement iteration over a packed array
// net returns - its element children, in declaration order.
std::vector<VpiHandle> VpiPackedArrayNetElements(VpiHandle packed_array_net);

// §37.16 detail 33: vpiStructUnionMember is TRUE for a net or array net that is a
// direct member of a struct net or union net (its vpiParent is a struct/union
// net), FALSE for any other net, and is not defined for a net bit (reported
// FALSE).
bool VpiNetStructUnionMember(VpiHandle net);

// §37.16 detail 34: vpiName of a net - the leaf member with its own index/slice
// but none of its struct/union-net prefixes. Reuses §37.17's name-parts shape.
std::string VpiNetName(const VpiVariableNameParts& parts);

// §37.16 detail 34: vpiDecompile of a net - the struct/union-net prefixes joined
// to the member (and its index/slice) without the top-level scope, so it
// resolves for any non-top-level scope context.
std::string VpiNetDecompile(const VpiVariableNameParts& parts);

// §37.16 detail 34: vpiFullName of a net - the top-level scope prefixed to the
// decompile form.
std::string VpiNetFullName(const VpiVariableNameParts& parts);

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

// §37.11 detail 2: the ranges vpi_iterate(vpiRange, instance_array) returns, one
// per declared dimension, beginning with the leftmost range of the declaration
// and running through the rightmost. Each dimension routes through §37.22's
// empty-range rule.
std::vector<VpiRangeDesc> VpiInstanceArrayRanges(
    const std::vector<VpiArrayDimension>& dims);

// §37.11 detail 2: vpiLeftRange of an instance array - the left bound of the
// leftmost dimension of a (possibly multidimensional) array. NULL when the array
// has no dimensions or that leftmost range is empty (§37.22).
VpiHandle VpiInstanceArrayLeftRange(const std::vector<VpiArrayDimension>& dims);

// §37.11 detail 2: vpiRightRange of an instance array, the mirror of
// VpiInstanceArrayLeftRange.
VpiHandle VpiInstanceArrayRightRange(const std::vector<VpiArrayDimension>& dims);

struct VpiVectorVal {
  uint32_t aval;
  uint32_t bval;
};

// §38.15 (Figure 38-9 element): one strength descriptor per vector bit. logic
// carries the vpi0/vpi1/vpiX/vpiZ value; s0 and s1 carry the drive/charge
// strength of the 0 and 1 components.
struct VpiStrengthVal {
  int logic = 0;
  int s0 = 0;
  int s1 = 0;
};

struct VpiValue {
  int format = 0;
  union {
    int integer;
    double real;
    const char* str;
    int scalar;
    VpiVectorVal* vector;
    VpiStrengthVal* strength;
  } value = {};
};

struct VpiTime {
  int type = 0;
  uint32_t high = 0;
  uint32_t low = 0;
  double real = 0.0;
};

// §38.10 (Figure 38-3): the delay structure exchanged with vpi_get_delays()
// (and vpi_put_delays()). `da` is an application-allocated array of VpiTime
// entries the routine fills with delay values; no_of_delays selects how many
// of the object's delays to retrieve; time_type selects the form of each value
// written into da; mtm_flag and pulsere_flag together select how many entries
// each delay occupies and what they hold (see Table 38-2). append_flag is only
// meaningful when putting delays.
struct VpiDelay {
  VpiTime* da = nullptr;
  int no_of_delays = 0;
  int time_type = 0;
  int mtm_flag = 0;
  int append_flag = 0;
  int pulsere_flag = 0;
};

struct VpiCbData {
  int reason = 0;
  // §38.36 (Figure 38-17): the application routine the simulator invokes when it
  // executes the callback; it is passed a pointer to this s_cb_data structure.
  int (*cb_rtn)(VpiCbData*) = nullptr;
  VpiHandle obj = nullptr;
  VpiTime* time = nullptr;
  VpiValue* value = nullptr;
  int index = 0;
  void* user_data = nullptr;
};

struct VpiErrorInfo {
  int state = 0;
  int level = 0;
  const char* message = nullptr;
  const char* product = nullptr;
  const char* code = nullptr;
  const char* file = nullptr;
  int line = 0;
};

struct VpiVlogInfo {
  int argc = 0;
  const char** argv = nullptr;
  const char* product = nullptr;
  const char* version = nullptr;
};

constexpr int kVpiSysTask = 1;
constexpr int kVpiSysFunc = 2;

// §38.37.1: the value kinds a system function may declare through the
// sysfunctype field. Only one of these may be named, and only when the system
// task/function was registered as a vpiSysFunc.
constexpr int kVpiIntFunc = 1;
constexpr int kVpiRealFunc = 2;
constexpr int kVpiTimeFunc = 3;
constexpr int kVpiSizedFunc = 4;
constexpr int kVpiSizedSignedFunc = 5;

// §38.37.1: a sized system function (vpiSizedFunc/vpiSizedSignedFunc) whose
// registration supplies no sizetf application returns a value 32 bits wide.
constexpr int kVpiDefaultSizedFuncBits = 32;

struct VpiSystfData {
  int type = 0;
  int sysfunctype = 0;
  const char* tfname = nullptr;
  int (*calltf)(const char*) = nullptr;
  int (*compiletf)(const char*) = nullptr;
  int (*sizetf)(const char*) = nullptr;
  void* user_data = nullptr;
};

// §38.37.1: the three points in the tool's lifetime that drive the callback
// applications named in a s_vpi_systf_data record.
enum class VpiSystfCallback { kCompiletf, kSizetf, kCalltf };

// §38.37.1 (tfname rule): whether a candidate system task/function name is a
// well-formed name as it would be written in SystemVerilog source - it begins
// with a dollar sign and is followed by one or more characters that are legal in
// a SystemVerilog simple identifier (A-Z, a-z, 0-9, underscore, dollar sign). A
// bare "$", an empty string, or any other character makes the name ill-formed.
bool VpiSystfNameIsValid(const char* tfname);

// §38.37.1 (sysfunctype rule): the value kind a registration declares for a
// system function. sysfunctype is meaningful only when the record was
// registered as a vpiSysFunc; for a system task it does not apply, so this
// reports 0 (no return-value kind) regardless of the stored field.
int VpiSystfReturnType(const VpiSystfData& data);

// §38.37.1: whether a given callback application fires while the simulation data
// structure is being compiled or built (true for compiletf and sizetf) rather
// than on every invocation during simulation execution (false for calltf).
bool VpiSystfCallbackFiresAtBuild(VpiSystfCallback callback);

// §38.37.1: invoke one of the systf callback applications. Every callback
// receives exactly one argument - the registration's user_data field, passed as
// a PLI_BYTE8 * - and a null function pointer (a field left unused) is simply
// skipped, returning 0.
int VpiSystfInvoke(int (*routine)(const char*), void* user_data);

// §38.37.1 (sizetf rule): whether the sizetf application is to be called for a
// registration. It is called only for a system function (vpiSysFunc) whose
// sysfunctype is vpiSizedFunc or vpiSizedSignedFunc; for anything else sizetf is
// never invoked.
bool VpiSystfSizetfIsCalled(const VpiSystfData& data);

// §38.37.1: the bit width a sized system function reports. When sizetf is to be
// called and a sizetf application is present it supplies the width (receiving
// user_data as its PLI_BYTE8 * argument); a sized function with no sizetf
// defaults to 32 bits.
int VpiSystfResultSizeBits(const VpiSystfData& data);

// §36.10.2: the tool-lifecycle phases that gate which VPI routines a PLI
// application may call. kStartup is the window in which the
// vlog_startup_routines[] array executes and very little functionality is
// available; kSizetf is the phase immediately after, when the sizetf routines
// run for user-defined system functions and no access beyond the startup phase
// is permitted; kFull begins once the cbEndOfCompile callbacks are called, from
// which point until the tool finishes all functionality is available.
enum class VpiToolPhase { kStartup, kSizetf, kFull };

// §36.10.2: whether a phase restricts VPI functionality. The startup phase and
// the sizetf phase that follows it both restrict it (the sizetf phase permits no
// access beyond the startup phase); only the full phase makes all functionality
// available.
bool VpiPhaseRestrictsFunctionality(VpiToolPhase phase);

// §36.10.2: the VPI routines whose availability the startup-phase restriction
// distinguishes. The two registration routines are the only ones callable while
// the vlog_startup_routines[] array executes; the others stand in for the bulk
// of the interface that is unavailable until the full phase.
enum class VpiRoutine {
  kRegisterSystf,
  kRegisterCb,
  kGetValue,
  kPutValue,
  kIterate,
};

// §36.10.2: whether a routine may be called during the startup phase. Only
// vpi_register_systf() and vpi_register_cb() are available at that time; every
// other VPI routine is not.
bool VpiRoutineAvailableInStartup(VpiRoutine routine);

// §36.10.2: whether vpi_register_cb() may be called for a given reason while
// functionality is restricted. During the startup phase (and the sizetf phase,
// which adds no access) the callback may be registered only for cbEndOfCompile,
// cbStartOfSimulation, cbEndOfSimulation, cbUnresolvedSystf, cbError, or
// cbPLIError.
bool VpiStartupCallbackReasonAllowed(int reason);

// §38.19: whether an object type carries the "access by index" property - the
// property the reference object of vpi_handle_by_index() must have. An object
// has it when one of its relationships selects a sub-object by an index number:
// a module indexes its ports, a net or reg indexes its bits, and an array or
// memory indexes its elements or words. An object type without the property
// cannot anchor a SystemVerilog index select, so it cannot serve as the
// reference object.
bool VpiHasAccessByIndex(int type);

class VpiContext {
 public:
  VpiContext() = default;
  ~VpiContext();

  void Attach(SimContext& sim_ctx);

  void SetScheduler(Scheduler* sched) { scheduler_ = sched; }

  VpiHandle RegisterSystf(VpiSystfData* data);

  // §38.12: report the registration of the system task or system function
  // callback denoted by `obj` into the application-allocated structure
  // `systf_data_p`. The structure's memory belongs to the caller; this routine
  // only writes the stored s_vpi_systf_data fields into it. A null handle, a
  // null destination, or a handle that does not name a registered system
  // task/function callback leaves the destination untouched.
  void GetSystfInfo(VpiHandle obj, VpiSystfData* systf_data_p);

  // §38.13: write the relevant simulation time into the application-allocated
  // structure `time_p`. The caller selects the form through `time_p->type`:
  // vpiSimTime delivers the raw 64-bit count in high/low; vpiScaledRealTime
  // delivers a real scaled to the object's timescale. A null obj uses the
  // simulation time unit; a time queue object reports the scheduled time of the
  // next future event, also in the simulation time unit. The structure's memory
  // belongs to the caller, so the routine only fills it and never allocates. A
  // null `time_p` leaves nothing to do.
  void GetTime(VpiHandle obj, VpiTime* time_p);

  // §38.10: retrieve the delays or pulse limits of `obj` into the
  // application-allocated structure `delay_p`. delay_p->no_of_delays selects
  // how many of the object's delays to retrieve and must be legal for the
  // object's category; delay_p->time_type controls the form of every value
  // written, and the type field of each da entry is ignored; delay_p->mtm_flag
  // and delay_p->pulsere_flag select the per-delay layout (Table 38-2). The
  // structure and its da array belong to the caller, so the routine only fills
  // them. A null delay_p, a null obj, or a null da leaves nothing to do; an
  // illegal no_of_delays records an error and writes nothing.
  void GetDelays(VpiHandle obj, VpiDelay* delay_p);

  // §38.13: set the simulation time unit, as a base-ten exponent of one second
  // (the unit the scheduler counts ticks in). vpi_get_time() uses it both as the
  // scaling reference for a scaled-real result and as the unit reported for a
  // null obj or a time queue object.
  void SetSimTimeUnit(int exponent) { sim_time_unit_ = exponent; }

  // §38.13: create a time queue object so vpi_get_time() can report the
  // scheduled time of the next future event.
  VpiHandle CreateTimeQueue();

  // §38.21: return a handle to the object named `name`, which may be a simple
  // or a hierarchical name. With a null scope the name is searched for from the
  // top level of the design hierarchy; with a scope the search is confined to
  // that scope's contents. A protected scope object, or a hierarchical name
  // that passes through a protected scope, makes the call an error (no handle).
  VpiHandle HandleByName(const char* name, VpiHandle scope);
  VpiHandle HandleByIndex(int index, VpiHandle parent);

  // §38.20: return a handle to the index-selected subobject of `parent` named
  // by the `num_index` indices in `index_array`. Like vpi_handle_by_index(),
  // the reference object must carry the access-by-index property and must not be
  // protected, or the call is an error. The indices are applied leftmost first,
  // following the array dimension declaration from the leftmost to the rightmost
  // range, optionally ending in a bit-select index. When the indices do not form
  // a legal SystemVerilog index select expression the result is a null handle.
  VpiHandle HandleByMultiIndex(int num_index, const int* index_array,
                               VpiHandle parent);
  VpiHandle Handle(int type, VpiHandle ref);
  VpiHandle Iterate(int type, VpiHandle ref);
  VpiHandle Scan(VpiHandle iterator);
  void GetValue(VpiHandle obj, VpiValue* value);
  VpiHandle PutValue(VpiHandle obj, VpiValue* value, VpiTime* time, int flags);
  VpiHandle RegisterCb(VpiCbData* data);
  int RemoveCb(VpiHandle cb_handle);
  int ExecuteCallback(VpiHandle cb_handle);
  void RegisterCbValueChange(const VpiCbData& data);

  // §38.36.3: deliver every active callback registered for the given action or
  // feature reason. Each routine receives a copy of its s_cb_data whose reason
  // field holds the reason for the callback; when a non-null obj or user_data is
  // supplied the simulator fills that field before the routine runs (for
  // example, the timing-check handle for cbTchkViolation, the new scope handle
  // for cbInteractiveScopeChange, or the unresolved name for cbUnresolvedSystf).
  // Returns how many callbacks were delivered.
  int DispatchCallbacks(int reason, VpiHandle obj = nullptr,
                        void* user_data = nullptr);

  // §38.36.3: a reset delivers cbStartOfReset at the start of the operation and
  // cbEndOfReset once it has completed. This is the single path used whether the
  // reset was requested directly or through vpi_control(vpiReset, ...).
  int DispatchReset();

  // §38.36.3: a restart first removes every registered callback except the
  // restart callbacks, then delivers cbStartOfRestart followed by cbEndOfRestart,
  // so the only callbacks that exist across a restart are those two.
  int DispatchRestart();

  int Get(int property, VpiHandle obj);

  // §37.10 detail 7: the smallest time precision over every module object the
  // context knows about, used to answer vpi_get(vpiTimePrecision/vpiTimeUnit)
  // for a null handle.
  int SmallestModuleTimePrecision() const;

  const char* GetStr(int property, VpiHandle obj);
  int FreeObject(VpiHandle obj);
  // §38.4: vpi_control() passes an operation-specific request from the PLI
  // application to the simulator. arg0..arg2 carry the operation's additional
  // integer arguments (the diagnostic level for vpiStop/vpiFinish, or the
  // stop/reset/diagnostics values for vpiReset); scope carries the vpiHandle
  // argument of vpiSetInteractiveScope. Returns 1 on success, 0 on failure.
  int Control(int operation, int arg0 = 0, int arg1 = 0, int arg2 = 0,
              VpiHandle scope = nullptr);
  bool ChkError(VpiErrorInfo* info);
  void GetVlogInfo(VpiVlogInfo* info);
  VpiHandle HandleMulti(int type, VpiHandle ref1, VpiHandle ref2);

  VpiHandle CreateModule(std::string_view name, std::string full_name);

  VpiHandle CreatePort(std::string_view name, int direction, VpiHandle parent);

  VpiHandle CreateParameter(std::string_view name, int int_value);

  // §37.49: register an assertion object under one of the assertion-class kinds
  // so that it is reachable as a top-level assertion (the circle relation) by a
  // null-referenced vpi_iterate(vpiAssertion, NULL).
  VpiHandle CreateAssertion(std::string_view name, int type);

  VpiHandle CreateNetObj(std::string_view name, Net* net_ptr, int width);

  const std::vector<VpiSystfData>& RegisteredSystfs() const { return systfs_; }

  const std::vector<VpiCbData>& RegisteredCallbacks() const {
    return callbacks_;
  }

  // §36.9.1: the registration of system tasks shall occur prior to elaboration
  // or the resolution of references. Marking elaboration as started closes the
  // window in which RegisterSystf will accept new registrations.
  void MarkElaborationStarted() { elaboration_started_ = true; }
  bool ElaborationStarted() const { return elaboration_started_; }

  // §36.10.2: the tool-lifecycle phase the VPI interface is currently in. It
  // gates which routines and callback reasons a PLI application may use. The
  // default is the full phase, so ordinary (post-compile) VPI use is
  // unrestricted; InvokeVlogStartupRoutines narrows it to the startup phase
  // while the vlog_startup_routines[] array executes.
  void SetToolPhase(VpiToolPhase phase) { tool_phase_ = phase; }
  VpiToolPhase ToolPhase() const { return tool_phase_; }

  bool StopRequested() const { return stop_requested_; }
  bool FinishRequested() const { return finish_requested_; }

  // §38.4: the diagnostic message level vpi_control() forwarded with the most
  // recent vpiStop/vpiFinish request (the same value $stop/$finish would carry,
  // see 20.2).
  int StopDiagLevel() const { return stop_diag_level_; }
  int FinishDiagLevel() const { return finish_diag_level_; }

  // §38.4: a reset requested through vpi_control(vpiReset, ...) and the three
  // arguments it carried (the same values passed to the $reset task, see D.8).
  bool ResetRequested() const { return reset_requested_; }
  int ResetStopValue() const { return reset_stop_value_; }
  int ResetResetValue() const { return reset_reset_value_; }
  int ResetDiagValue() const { return reset_diag_value_; }

  // §38.4: the scope vpi_control(vpiSetInteractiveScope, ...) most recently made
  // the tool's interactive scope.
  VpiHandle InteractiveScope() const { return interactive_scope_; }

  // §37.43 detail 4: record which frame is the one currently active. There is at
  // most one active frame at a time in a given thread, and an application reaches
  // it through vpi_handle(vpiFrame, NULL) (see Handle).
  void SetActiveFrame(VpiHandle frame) { active_frame_ = frame; }
  VpiHandle ActiveFrame() const { return active_frame_; }

  const VpiErrorInfo& LastError() const { return last_error_; }

  // §38.2: the error status is reset by any VPI routine call except
  // vpi_chk_error(). The C entry points clear the pending error here on entry
  // before doing their work, so vpi_chk_error() reports only the outcome of the
  // most recent routine; a failing routine then records a fresh error.
  void ResetErrorStatus() { last_error_ = {}; }

 private:
  VpiHandle AllocObject();

  std::vector<VpiSystfData> systfs_;
  std::vector<VpiCbData> callbacks_;
  std::vector<VpiHandle> cb_handles_;
  std::unordered_map<std::string_view, VpiObject*> object_map_;
  std::vector<VpiObject*> all_objects_;
  Scheduler* scheduler_ = nullptr;
  // §38.13: the simulation time unit (base-ten exponent of one second) the
  // scheduler's tick count is expressed in; the reference vpi_get_time() scales
  // a scaled-real result against.
  int sim_time_unit_ = 0;
  bool elaboration_started_ = false;
  // §36.10.2: see SetToolPhase. Defaults to the full phase so VPI use outside
  // the startup window is unrestricted.
  VpiToolPhase tool_phase_ = VpiToolPhase::kFull;
  bool stop_requested_ = false;
  bool finish_requested_ = false;
  int stop_diag_level_ = 0;
  int finish_diag_level_ = 0;
  bool reset_requested_ = false;
  int reset_stop_value_ = 0;
  int reset_reset_value_ = 0;
  int reset_diag_value_ = 0;
  VpiHandle interactive_scope_ = nullptr;
  // §37.43 detail 4: the frame currently active, returned by
  // vpi_handle(vpiFrame, NULL).
  VpiHandle active_frame_ = nullptr;
  VpiErrorInfo last_error_ = {};
  std::string product_ = "DeltaHDL";
  std::string version_ = "0.1.0";

  std::vector<std::string> str_pool_;

  // §38.15: vpi_get_value() owns the memory for the vector arm of the value
  // union; each retrieval keeps its s_vpi_vecval array alive here until the
  // context is torn down. Inner vectors own their own storage, so growing the
  // outer pool never invalidates a previously handed-out array pointer.
  std::vector<std::vector<VpiVectorVal>> vec_pool_;

  // §38.15: likewise the routine owns the s_vpi_strengthval array handed back
  // for the strength arm of the value union.
  std::vector<std::vector<VpiStrengthVal>> strength_pool_;
};

Region RegionForPliCallback(int reason);

bool IsOneShotPliCallback(int reason);

VpiContext& GetGlobalVpiContext();
void SetGlobalVpiContext(VpiContext* ctx);

// §36.9.1: the intended use model places a reference to a registration
// routine in the vlog_startup_routines[] array. Each entry is a function that
// takes no arguments and returns nothing, and the array is conventionally
// null-terminated.
using VlogStartupRoutine = void (*)();

// §36.9.1: walking the vlog_startup_routines[] array calls each non-null
// entry in order, giving each routine its chance to register user-defined
// system tasks and functions before elaboration begins. Iteration stops at
// the first null sentinel.
void InvokeVlogStartupRoutines(VlogStartupRoutine* routines);

}

using vpiHandle = delta::VpiHandle;
using s_vpi_value = delta::VpiValue;
using s_vpi_time = delta::VpiTime;
using s_cb_data = delta::VpiCbData;
using s_vpi_systf_data = delta::VpiSystfData;
using s_vpi_vecval = delta::VpiVectorVal;
using SVpiErrorInfo = delta::VpiErrorInfo;
using SVpiVlogInfo = delta::VpiVlogInfo;

#define vpiModule 32
#define vpiNet 36
#define vpiReg 48
#define vpiPort 44
#define vpiParameter 41
#define vpiCallback 107

#define vpiBinStrVal 1
#define vpiOctStrVal 2
#define vpiHexStrVal 3
#define vpiScalarVal 4
#define vpiIntVal 5
#define vpiRealVal 6
#define vpiStringVal 7
#define vpiTimeVal 8
#define vpiVectorVal 9

#define vpiSimTime 1
#define vpiScaledRealTime 2

#define cbValueChange 1
#define cbReadWriteSynch 2
#define cbEndOfSimulation 3
#define cbStmt 4
#define cbAtStartOfSimTime 5
#define cbReadOnlySynch 6
#define cbAfterDelay 7
#define cbNextSimTime 8
#define cbNBASynch 9
#define cbAtEndOfSimTime 10

// §38.36.3 simulator action/feature callback reasons (mirror of the kCb* values).
#define cbEndOfCompile 11
#define cbStartOfSimulation 12
#define cbError 13
#define cbPLIError 14
#define cbTchkViolation 15
#define cbSignal 16
#define cbStartOfSave 17
#define cbEndOfSave 18
#define cbStartOfRestart 19
#define cbEndOfRestart 20
#define cbStartOfReset 21
#define cbEndOfReset 22
#define cbEnterInteractive 23
#define cbExitInteractive 24
#define cbInteractiveScopeChange 25
#define cbUnresolvedSystf 26

#define vpiType 1
#define vpiName 2
#define vpiFullName 3
#define vpiSize 4
#define vpiDirection 5
#define vpiDefName 6
#define vpiLibrary 67
#define vpiConfig 70
#define vpiCell 71

#define vpiInput 1
#define vpiOutput 2
#define vpiInout 3

#define vpiNoDelay 1
#define vpiInertialDelay 2
#define vpiTransportDelay 3
#define vpiPureTransportDelay 4

#define vpiFinish 66
#define vpiStop 67
#define vpiReset 68

#define vpi0 0
#define vpi1 1
#define vpiX 2
#define vpiZ 3

// §38.2 Table 38-1: vpi_chk_error() severity levels, lowest to highest.
#define vpiNotice 1
#define vpiWarning 2
#define vpiError 3
#define vpiSystem 4
#define vpiInternal 5

#define vpiSysTask 1
#define vpiSysFunc 2

// ----------------------------------------------------------------------------
// §K.2 (Annex K, normative): vpi_user.h source code. The constants, sized
// portability typedefs and value/delay/strength structures below complete
// the include file that every SystemVerilog simulator is required to
// provide. Symbols already supplied by other clauses (object kinds,
// callback reasons, control codes, value formats, etc.) are not repeated.
// ----------------------------------------------------------------------------
// §K.2: the vpi_user.h portability layer fixes the width of the integer types
// every VPI routine and structure is expressed in. These aliases are the
// DeltaHDL realization of those typedefs.
using PLI_INT32 = int32_t;
using PLI_UINT32 = uint32_t;
using PLI_INT64 = int64_t;
using PLI_UINT64 = uint64_t;
using PLI_INT16 = short;
using PLI_UINT16 = unsigned short;
using PLI_BYTE8 = char;
using PLI_UBYTE8 = unsigned char;

#define vpiAlways 1
#define vpiAssignStmt 2
#define vpiAssignment 3
#define vpiBegin 4
#define vpiCase 5
#define vpiCaseItem 6
#define vpiConstant 7
#define vpiContAssign 8
#define vpiDeassign 9
#define vpiDefParam 10
#define vpiDelayControl 11
#define vpiDisable 12
#define vpiEventControl 13
#define vpiEventStmt 14
#define vpiFor 15
#define vpiForce 16
#define vpiForever 17
#define vpiFork 18
#define vpiFuncCall 19
#define vpiFunction 20
#define vpiGate 21
#define vpiIf 22
#define vpiIfElse 23
#define vpiInitial 24
#define vpiIntegerVar 25
#define vpiInterModPath 26
#define vpiIterator 27
#define vpiIODecl 28
#define vpiMemory 29
#define vpiMemoryWord 30
#define vpiModPath 31
#define vpiNamedBegin 33
#define vpiNamedEvent 34
#define vpiNamedFork 35
#define vpiNetBit 37
#define vpiNullStmt 38
#define vpiOperation 39
#define vpiParamAssign 40
#define vpiPartSelect 42
#define vpiPathTerm 43
#define vpiPortBit 45
#define vpiPrimTerm 46
#define vpiRealVar 47
#define vpiRegBit 49
#define vpiRelease 50
#define vpiRepeat 51
#define vpiRepeatControl 52
#define vpiSchedEvent 53
#define vpiSpecParam 54
#define vpiSwitch 55
#define vpiSysFuncCall 56
#define vpiSysTaskCall 57
#define vpiTableEntry 58
#define vpiTask 59
#define vpiTaskCall 60
#define vpiTchk 61
#define vpiTchkTerm 62
#define vpiTimeVar 63
#define vpiTimeQueue 64
#define vpiUdp 65
#define vpiUdpDefn 66
#define vpiUserSystf 67
#define vpiVarSelect 68
#define vpiWait 69
#define vpiWhile 70
#define vpiAttribute 105
#define vpiBitSelect 106
#define vpiDelayTerm 108
#define vpiDelayDevice 109
#define vpiFrame 110
#define vpiGateArray 111
#define vpiModuleArray 112
#define vpiPrimitiveArray 113
#define vpiNetArray 114
#define vpiRange 115
#define vpiRegArray 116
#define vpiSwitchArray 117
#define vpiUdpArray 118
#define vpiContAssignBit 128
#define vpiNamedEventArray 129
#define vpiIndexedPartSelect 130
#define vpiGenScopeArray 133
#define vpiGenScope 134
#define vpiGenVar 135
#define vpiCondition 71
#define vpiDelay 72
#define vpiElseStmt 73
#define vpiForIncStmt 74
#define vpiForInitStmt 75
#define vpiHighConn 76
#define vpiLhs 77
#define vpiIndex 78
#define vpiLeftRange 79
#define vpiLowConn 80
#define vpiParent 81
#define vpiRhs 82
#define vpiRightRange 83
#define vpiScope 84
#define vpiSysTfCall 85
#define vpiTchkDataTerm 86
#define vpiTchkNotifier 87
#define vpiTchkRefTerm 88
#define vpiArgument 89
#define vpiBit 90
#define vpiDriver 91
#define vpiInternalScope 92
#define vpiLoad 93
#define vpiModDataPathIn 94
#define vpiModPathIn 95
#define vpiModPathOut 96
#define vpiOperand 97
#define vpiPortInst 98
#define vpiProcess 99
#define vpiVariables 100
#define vpiUse 101
#define vpiExpr 102
#define vpiPrimitive 103
#define vpiStmt 104
#define vpiActiveTimeFormat 119
#define vpiInTerm 120
#define vpiInstanceArray 121
#define vpiLocalDriver 122
#define vpiLocalLoad 123
#define vpiOutTerm 124
#define vpiPorts 125
#define vpiSimNet 126
#define vpiTaskFunc 127
#define vpiBaseExpr 131
#define vpiWidthExpr 132
#define vpiAutomatics 136
#define vpiUndefined -1
#define vpiFile 5
#define vpiLineNo 6
#define vpiTopModule 7
#define vpiCellInstance 8
#define vpiProtected 10
#define vpiTimeUnit 11
#define vpiTimePrecision 12
#define vpiDefNetType 13
#define vpiUnconnDrive 14
#define vpiHighZ 1
#define vpiPull1 2
#define vpiPull0 3
#define vpiDefFile 15
#define vpiDefLineNo 16
#define vpiDefDelayMode 47
#define vpiDelayModeNone 1
#define vpiDelayModePath 2
#define vpiDelayModeDistrib 3
#define vpiDelayModeUnit 4
#define vpiDelayModeZero 5
#define vpiDelayModeMTM 6
#define vpiDefDecayTime 48
#define vpiScalar 17
#define vpiVector 18
#define vpiExplicitName 19
#define vpiMixedIO 4
#define vpiNoDirection 5
#define vpiConnByName 21
#define vpiNetType 22
#define vpiWire 1
#define vpiWand 2
#define vpiWor 3
#define vpiTri 4
#define vpiTri0 5
#define vpiTri1 6
#define vpiTriReg 7
#define vpiTriAnd 8
#define vpiTriOr 9
#define vpiSupply1 10
#define vpiSupply0 11
#define vpiNone 12
#define vpiUwire 13
#define vpiNettypeNet 14
#define vpiNettypeNetSelect 15
#define vpiInterconnect 16
#define vpiExplicitScalared 23
#define vpiExplicitVectored 24
#define vpiExpanded 25
#define vpiImplicitDecl 26
#define vpiChargeStrength 27
#define vpiArray 28
#define vpiPortIndex 29
#define vpiTermIndex 30
#define vpiStrength0 31
#define vpiStrength1 32
#define vpiPrimType 33
#define vpiAndPrim 1
#define vpiNandPrim 2
#define vpiNorPrim 3
#define vpiOrPrim 4
#define vpiXorPrim 5
#define vpiXnorPrim 6
#define vpiBufPrim 7
#define vpiNotPrim 8
#define vpiBufif0Prim 9
#define vpiBufif1Prim 10
#define vpiNotif0Prim 11
#define vpiNotif1Prim 12
#define vpiNmosPrim 13
#define vpiPmosPrim 14
#define vpiCmosPrim 15
#define vpiRnmosPrim 16
#define vpiRpmosPrim 17
#define vpiRcmosPrim 18
#define vpiRtranPrim 19
#define vpiRtranif0Prim 20
#define vpiRtranif1Prim 21
#define vpiTranPrim 22
#define vpiTranif0Prim 23
#define vpiTranif1Prim 24
#define vpiPullupPrim 25
#define vpiPulldownPrim 26
#define vpiSeqPrim 27
#define vpiCombPrim 28
#define vpiPolarity 34
#define vpiDataPolarity 35
#define vpiPositive 1
#define vpiNegative 2
#define vpiUnknown 3
#define vpiEdge 36
#define vpiNoEdge 0x00
#define vpiEdge01 0x01
#define vpiEdge10 0x02
#define vpiEdge0x 0x04
#define vpiEdgex1 0x08
#define vpiEdge1x 0x10
#define vpiEdgex0 0x20
#define vpiPosedge (vpiEdgex1 | vpiEdge01 | vpiEdge0x)
#define vpiNegedge (vpiEdgex0 | vpiEdge10 | vpiEdge1x)
#define vpiAnyEdge (vpiPosedge | vpiNegedge)
#define vpiPathType 37
#define vpiPathFull 1
#define vpiPathParallel 2
#define vpiTchkType 38
#define vpiSetup 1
#define vpiHold 2
#define vpiPeriod 3
#define vpiWidth 4
#define vpiSkew 5
#define vpiRecovery 6
#define vpiNoChange 7
#define vpiSetupHold 8
#define vpiFullskew 9
#define vpiRecrem 10
#define vpiRemoval 11
#define vpiTimeskew 12
#define vpiOpType 39
#define vpiMinusOp 1
#define vpiPlusOp 2
#define vpiNotOp 3
#define vpiBitNegOp 4
#define vpiUnaryAndOp 5
#define vpiUnaryNandOp 6
#define vpiUnaryOrOp 7
#define vpiUnaryNorOp 8
#define vpiUnaryXorOp 9
#define vpiUnaryXNorOp 10
#define vpiSubOp 11
#define vpiDivOp 12
#define vpiModOp 13
#define vpiEqOp 14
#define vpiNeqOp 15
#define vpiCaseEqOp 16
#define vpiCaseNeqOp 17
#define vpiGtOp 18
#define vpiGeOp 19
#define vpiLtOp 20
#define vpiLeOp 21
#define vpiLShiftOp 22
#define vpiRShiftOp 23
#define vpiAddOp 24
#define vpiMultOp 25
#define vpiLogAndOp 26
#define vpiLogOrOp 27
#define vpiBitAndOp 28
#define vpiBitOrOp 29
#define vpiBitXorOp 30
#define vpiBitXNorOp 31
#define vpiBitXnorOp vpiBitXNorOp
#define vpiConditionOp 32
#define vpiConcatOp 33
#define vpiMultiConcatOp 34
#define vpiEventOrOp 35
#define vpiNullOp 36
#define vpiListOp 37
#define vpiMinTypMaxOp 38
#define vpiPosedgeOp 39
#define vpiNegedgeOp 40
#define vpiArithLShiftOp 41
#define vpiArithRShiftOp 42
#define vpiPowerOp 43
#define vpiConstType 40
#define vpiDecConst 1
#define vpiRealConst 2
#define vpiBinaryConst 3
#define vpiOctConst 4
#define vpiHexConst 5
#define vpiStringConst 6
#define vpiIntConst 7
#define vpiTimeConst 8
#define vpiBlocking 41
#define vpiCaseType 42
#define vpiCaseExact 1
#define vpiCaseX 2
#define vpiCaseZ 3
#define vpiNetDeclAssign 43
#define vpiFuncType 44
#define vpiIntFunc 1
#define vpiRealFunc 2
#define vpiTimeFunc 3
#define vpiSizedFunc 4
#define vpiSizedSignedFunc 5
#define vpiSysFuncType vpiFuncType
#define vpiSysFuncInt vpiIntFunc
#define vpiSysFuncReal vpiRealFunc
#define vpiSysFuncTime vpiTimeFunc
#define vpiSysFuncSized vpiSizedFunc
#define vpiUserDefn 45
#define vpiScheduled 46
#define vpiActive 49
#define vpiAutomatic 50

// §37.3.7: allocation-scheme property selector and its three return values. The
// selector (731) is a free property number; the return values share the small
// property-result namespace.
#define vpiAllocScheme 731
#define vpiAutomaticScheme 1
#define vpiDynamicScheme 2
#define vpiOtherScheme 3
#define vpiConstantSelect 53
#define vpiDecompile 54
#define vpiDefAttribute 55
#define vpiDelayType 56
#define vpiModPathDelay 1
#define vpiInterModPathDelay 2
#define vpiMIPDelay 3
#define vpiIteratorType 57
#define vpiOffset 60
#define vpiResolvedNetType 61
#define vpiSaveRestartID 62
#define vpiSaveRestartLocation 63
#define vpiValid 64
#define vpiValidFalse 0
#define vpiValidTrue 1
#define vpiSigned 65
#define vpiLocalParam 70
#define vpiModPathHasIfNone 71
#define vpiIndexedPartSelectType 72
#define vpiPosIndexed 1
#define vpiNegIndexed 2
#define vpiIsMemory 73
#define vpiIsProtected 74
#define vpiSetInteractiveScope 69
#define VPI_MCD_STDOUT 0x00000001
#define vpiSuppressTime 3
#define vpiSupplyDrive 0x80
#define vpiStrongDrive 0x40
#define vpiPullDrive 0x20
#define vpiWeakDrive 0x08
#define vpiLargeCharge 0x10
#define vpiMediumCharge 0x04
#define vpiSmallCharge 0x02
#define vpiHiZ 0x01
#define vpiDecStrVal 3
#define vpiStrengthVal 10
#define vpiObjTypeVal 12
#define vpiSuppressVal 13
#define vpiShortIntVal 14
#define vpiLongIntVal 15
#define vpiShortRealVal 16
#define vpiRawTwoStateVal 17
#define vpiRawFourStateVal 18
#define vpiForceFlag 5
#define vpiReleaseFlag 6
#define vpiCancelEvent 7
#define vpiReturnEvent 0x1000
#define vpiUserAllocFlag 0x2000
#define vpiOneValue 0x4000
#define vpiPropagateOff 0x8000
#define vpiH 4
#define vpiL 5
#define vpiDontCare 6
#define vpiCompile 1
#define vpiPLI 2
#define vpiRun 3
#define cbForce 3
#define cbRelease 4
#define cbAssign 25
#define cbDeassign 26
#define cbDisable 27

// §37.17 Variables / §37.22 Object range: the variable object kinds (vpiBitVar,
// vpiStructVar, ...), the backward-compatibility aliases of detail 19 (vpiVarBit,
// vpiLogicVar, vpiArrayVar), and the related properties (vpiArrayType,
// vpiRandType, vpiVisibility, vpiArrayMember, vpiStructUnionMember, ...) are all
// defined by the Annex M source listing in sv_vpi_user.h. The range relations
// (vpiSize, vpiLeftRange, vpiRightRange, vpiRange, vpiBit, vpiIndex, vpiParent,
// vpiScalar, vpiVector, vpiConstantSelect, vpiDecompile) are defined above. The
// helpers declared below apply the clause rules on top of those constants.

// §K.2: delay structure exchanged with the delay-processing routines. The
// definition lives inside the delta namespace (VpiDelay) so the simulator's
// implementation can name it directly; these aliases expose it under the
// standard PLI spellings.
using s_vpi_delay = delta::VpiDelay;
using p_vpi_delay = delta::VpiDelay*;

// §K.2: scalar strength value. logic holds a vpi0/vpi1/vpiX/vpiZ code and the
// s0/s1 fields carry the drive/charge strength components.
typedef struct t_vpi_strengthval {
  PLI_INT32 logic = 0;
  PLI_INT32 s0 = 0;
  PLI_INT32 s1 = 0;
} s_vpi_strengthval, *p_vpi_strengthval;

// §K.2: aggregate value used by the array value routines. The format selects
// which arm of the union is live; flags carries vpiUserAllocFlag and friends.
typedef struct t_vpi_arrayvalue {
  PLI_UINT32 format = 0;
  PLI_UINT32 flags = 0;
  union {
    PLI_INT32* integers;
    PLI_INT16* shortints;
    PLI_INT64* longints;
    PLI_BYTE8* rawvals;
    s_vpi_vecval* vectors;
    s_vpi_time* times;
    double* reals;
    float* shortreals;
  } value = {};
} s_vpi_arrayvalue, *p_vpi_arrayvalue;


vpiHandle vpi_register_systf(s_vpi_systf_data* data);
void vpi_get_systf_info(vpiHandle obj, s_vpi_systf_data* systf_data_p);
void vpi_get_time(vpiHandle obj, s_vpi_time* time_p);
void vpi_get_delays(vpiHandle obj, p_vpi_delay delay_p);
vpiHandle VpiHandleC(int type, vpiHandle ref);
vpiHandle vpi_handle_by_name(const char* name, vpiHandle scope);
vpiHandle VpiHandleByIndexC(vpiHandle parent, int index);
vpiHandle VpiHandleByMultiIndexC(vpiHandle parent, int num_index,
                                 int* index_array);
vpiHandle VpiHandleMultiC(int type, vpiHandle ref1, vpiHandle ref2);
vpiHandle vpi_iterate(int type, vpiHandle ref);
vpiHandle vpi_scan(vpiHandle iterator);
void vpi_get_value(vpiHandle obj, s_vpi_value* value);
vpiHandle vpi_put_value(vpiHandle obj, s_vpi_value* value, s_vpi_time* time,
                        int flags);
vpiHandle vpi_register_cb(s_cb_data* data);
int VpiRemoveCbC(vpiHandle cb_handle);
int vpi_get(int property, vpiHandle obj);
const char* vpi_get_str(int property, vpiHandle obj);
int vpi_free_object(vpiHandle obj);
int VpiControlC(int operation, ...);
int VpiChkErrorC(SVpiErrorInfo* info);
void vpi_get_vlog_info(SVpiVlogInfo* info);
