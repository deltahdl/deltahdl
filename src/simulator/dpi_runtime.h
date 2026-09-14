#pragma once

#include <cstdint>
#include <deque>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/assertion_api.h"
#include "simulator/coverage_control.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/sva_engine_sequences.h"

namespace delta {

// §H.13: the value a scope's time unit or precision has where none is bound
// to it, in which case the simulation's apply.
inline constexpr int32_t kDpiNoTimescale = INT32_MIN;

struct DpiScope {
  std::string name;
  std::string_view module_name;
  void* user_data = nullptr;
  // §H.13: the time unit and time precision of the instance scope, each a
  // base-ten exponent of one second (-9 for ns), which svGetTime scales the
  // current time to and svGetTimeUnit and svGetTimePrecision report for the
  // scope; kDpiNoTimescale where the scope has none bound, the simulation
  // time unit then standing in as it does for a NULL scope.
  int32_t time_unit = kDpiNoTimescale;
  int32_t time_precision = kDpiNoTimescale;
};

// Annex H.14: how an import's declaration has its packed data arguments passed
// to the foreign code. IEEE Std 1800 marshals packed data into the canonical
// representation §H.10.1.2 defines. Accellera SystemVerilog 3.1a passes it by
// the opaque handle types svBitPackedArrRef and svLogicPackedArrRef instead —
// a reference to the simulator's own representation — and an implementation
// doing so "need not do any conversion or marshalling of data into the
// canonical format". §H.14 deprecates the SV3.1a semantics and lets a simulator
// decline them, so an import is passed its packed data in the canonical
// representation unless its declaration selects the other.
enum class DpiPackedArgPassing : uint8_t {
  kCanonical,
  kSv31aReference,
};

// §H.14.1: svDpiVersion() lets C code determine an implementation's support
// for the standard: a simulator supporting only the SV3.1a standard reports
// "SV3.1a", and users of one shall make use of the opaque handle types for
// all 2-state and 4-state arguments; an IEEE Std 1800 implementation reports
// "1800-2005" (§H.10.1.3), and with one users can make use of SV3.1a-
// compatible semantics on a per-function basis -- a declaration annotated
// "DPI" yields the SV3.1a argument passing semantics on the C side and one
// annotated "DPI-C" the IEEE Std 1800 semantics (§35.4, §35.5.4). svdpi.h may
// contain the definitions and prototypes SV3.1a-compliant packed data access
// uses, and an IEEE Std 1800 implementation is not obligated to provide
// them; where an implementation does not support the functionality, DPI C
// code may not successfully bind to it.
enum class DpiCompatibilityLevel : uint8_t { kIeee1800, kSv31a };

DpiCompatibilityLevel DpiCompatibilityLevelOf(std::string_view sv_dpi_version);
bool DpiOpaqueHandlesAreRequiredForAllPackedArguments(
    DpiCompatibilityLevel level);
DpiPackedArgPassing DpiPassingSemanticsOfSpecString(
    std::string_view dpi_spec_string);
bool DpiSv31aDefinitionsAreObligatoryInSvdpiH();
bool DpiCCodeMayFailToBind(bool implementation_supports_sv31a_functionality);

// §H.14.3: the source-level compatibility include file svdpi_src.h defines
// two symbols only, the macros SV_BIT_PACKED_ARRAY and SV_LOGIC_PACKED_ARRAY
// that declare variables representing SystemVerilog packed arrays of bit or
// logic, whose definitions are implementation-specific and define no array
// type. An application that does not need the file is binary compatible --
// its DPI C code runs on different simulators without recompilation -- and
// one that makes use of it has to be recompiled for each simulator it runs
// on.
enum class DpiApplicationCompatibility : uint8_t { kBinary, kSource };

DpiApplicationCompatibility DpiCompatibilityOfApplication(bool uses_svdpi_src);
bool DpiApplicationIsRecompiledPerSimulator(bool uses_svdpi_src);
uint32_t DpiSvdpiSrcSymbolCount();
bool DpiPackedArrayMacroMayDefineAnArrayType();

struct DpiRtFunction {
  std::string_view c_name;
  std::string_view sv_name;
  DataTypeKind return_type = DataTypeKind::kVoid;
  std::vector<DpiArg> args;
  DpiRtCallback impl;
  // §35.5.1.2: optional direction-aware implementation. When set,
  // CallImportWithArgs uses it so the foreign function can write its output
  // and inout formals.
  DpiRtArgCallback arg_impl;
  bool is_pure = false;
  bool is_context = false;
  // §H.2: true where the declaration imports a task -- a function implemented
  // in C that can in turn call exported tasks -- and false where it imports a
  // function, which §35.8 bars from calling one.
  bool is_task = false;
  // Annex H.14: the argument passing semantics this declaration selects for its
  // packed data arguments. The SV3.1a semantics are deprecated functionality a
  // simulator need not implement, so a declaration that does not ask for them
  // gets the canonical representation.
  DpiPackedArgPassing packed_arg_passing = DpiPackedArgPassing::kCanonical;
};

struct DpiRtExport {
  std::string_view c_name;
  std::string_view sv_name;
  // §35.5.3: the SystemVerilog scope where this export was declared. When
  // empty, the export is treated as callable from any chain scope (a
  // conservative default for code that doesn't yet record scopes).
  std::string scope_name;
  DpiRtCallback impl;
  // §35.7: every exported SystemVerilog function is a context function. The
  // flag is documentary at the type level and is normalized to true by
  // DpiRuntime::RegisterExport so callers that leave it unset still get the
  // spec-mandated behavior.
  bool is_context = true;
  // §35.8: true when this export names a SystemVerilog task rather than a
  // function. The runtime uses it to enforce that an imported function may
  // never invoke an exported task; see CallExportFromImport.
  bool is_task = false;
  // §35.2.2: the SystemVerilog types crossing when foreign code calls this
  // export in. An absent position and a kVoid result leave a value as it is.
  DataTypeKind return_type = DataTypeKind::kVoid;
  std::vector<DpiArg> args;
};

// §35.4: the name in the global name space that a declaration resolves to.
// Every imported subroutine resolves to a global symbol and every exported one
// defines a global symbol, named by the declaration's linkage name. "If a
// global name is not explicitly given, it shall be the same as the
// SystemVerilog subroutine name."
std::string_view DpiGlobalName(const DpiRtFunction& func);
std::string_view DpiGlobalName(const DpiRtExport& exp);

// §35.5.3: outcome of attempting to call a SystemVerilog export from inside
// a DPI import call chain. kOk means the call was permitted; kNoncontextChain
// reports the §35.5.3 error of a noncontext import trying to invoke an
// export. kScopeMismatch reports the §35.5.3 error of a context import call
// trying to invoke an export whose scope differs from the chain's current
// scope without first calling svSetScope. kFunctionCallsTask reports the
// §35.8 error of an imported function trying to invoke an exported task,
// which is never legal regardless of the chain's context property.
// kDisabledStateExportCall reports the §35.9 item d) error of an imported
// subroutine that has entered the disabled state trying to make any further
// call to an exported subroutine.
enum class DpiExportCallStatus : uint8_t {
  kOk,
  kNoncontextChain,
  kScopeMismatch,
  kFunctionCallsTask,
  kDisabledStateExportCall,
};

// §35.9: what a disable statement targets, relative to an exported subroutine
// that is unwinding because of it. The target decides the int value the
// exported task yields and whether the calling import enters the disabled
// state.
enum class DpiDisableTarget : uint8_t {
  // The exported subroutine is returning normally; no disable is in effect.
  kNone,
  // The disable targets the exported subroutine itself. Per §35.9 the parent
  // import is then not considered disabled and the task returns 0.
  kExportItself,
  // The disable targets a parent in the mixed-language call chain. The disable
  // is still propagating, so the calling import enters the disabled state and
  // the exported task returns 1.
  kAncestor,
};

// §35.9 disable-protocol view of the current thread's state. The public svdpi
// entry points svIsDisabledState() and svAckDisabledState() forward to these,
// so the disabled state the standard describes is observable through the very
// API functions it names. The state is per thread because a foreign routine
// queries it for its own execution context with no explicit handle.
bool DpiCurrentDisabledState();
void DpiSetCurrentDisabledState(bool disabled);
void DpiAckCurrentDisable();
bool DpiCurrentDisableAcknowledged();

// §H.9.3 scope-name registry. The svdpi entry points svGetScopeFromName() and
// svGetNameFromScope() consult this registry to translate between an opaque
// scope handle and the fully qualified name of an instance scope (a module,
// program, interface, or generate scope). In a full elaboration each such scope
// is registered here; the C API then hands out and reverses these handles.
//
// DpiRegisterScope is idempotent by name: registering the same name twice
// returns the same stable handle. DpiScopeFromName returns nullptr for a name
// that was never registered (the standard's "unrecognized scope name" → NULL).
// DpiNameFromScope returns the fully qualified name of a handle that originated
// here, or "" for a null or unrecognized handle (it never dereferences a
// pointer it did not create).
const DpiScope* DpiRegisterScope(std::string_view name);
const DpiScope* DpiScopeFromName(std::string_view name);
const char* DpiNameFromScope(const DpiScope* scope);

// §H.13: bind the time unit and precision of the instance scope a registered
// handle names, each a base-ten exponent of one second, so that svGetTime
// scales to the unit and svGetTimeUnit and svGetTimePrecision report the two
// for the scope. A handle the registry did not produce binds nothing.
// DpiScopeTimescale reads them back, answering false for an unrecognized
// handle, a NULL one, or a scope with no timescale bound -- the cases the
// simulation time unit stands in for.
void DpiSetScopeTimescale(const DpiScope* scope, int32_t time_unit,
                          int32_t time_precision);
bool DpiScopeTimescale(const DpiScope* scope, int32_t* time_unit,
                       int32_t* time_precision);

class DpiRuntime {
 public:
  void RegisterImport(DpiRtFunction func);
  const DpiRtFunction* FindImport(std::string_view sv_name) const;
  bool HasImport(std::string_view sv_name) const;
  uint32_t ImportCount() const;

  void RegisterExport(DpiRtExport exp);
  const DpiRtExport* FindExport(std::string_view sv_name) const;

  // §35.5.3: the instance of the export named `sv_name` that the instantiated
  // scope `scope_name` declares, or nullptr where that scope declares no export
  // of that name. §35.5.3 has one exported subroutine exist as several
  // instances after elaboration, one per instantiated scope that declares it,
  // because imports with diverse instantiated scopes can export the same
  // subroutine. FindExport answers by name alone and cannot tell those
  // instances apart, so it returns whichever was registered last.
  const DpiRtExport* FindExportInScope(std::string_view sv_name,
                                       std::string_view scope_name) const;
  bool HasExport(std::string_view sv_name) const;
  uint32_t ExportCount() const;

  // §35.4: the declaration resolving to the global symbol `global_name`, or
  // nullptr where none does. DPI subroutines "have their own global name space
  // of linkage names, different from compilation-unit scope name space", so a
  // SystemVerilog subroutine name is not a global name: a declaration giving a
  // linkage name is reachable here under that name and under no other.
  // FindImport and FindExport answer the other name space, keyed by the name
  // SystemVerilog calls the subroutine.
  const DpiRtFunction* FindImportByGlobalName(
      std::string_view global_name) const;
  const DpiRtExport* FindExportByGlobalName(std::string_view global_name) const;

  // §35.4: whether any imported or exported subroutine resolves to the global
  // symbol `global_name`. Imports and exports share one name space between
  // them, so this answers for both kinds of declaration.
  bool HasGlobalName(std::string_view global_name) const;

  // §35.4: how many distinct global symbols the declarations registered here
  // resolve to. "The same global subroutine can be referred to in multiple
  // import declarations in different scopes or/and with different SystemVerilog
  // names", so this falls below ImportCount() plus ExportCount() wherever
  // declarations share a linkage name.
  uint32_t GlobalNameCount() const;

  DpiArgValue CallImport(std::string_view sv_name,
                         const std::vector<DpiArgValue>& args) const;

  // §35.5.1.2: the value a foreign function receives for an output formal.
  // Because an imported function shall not assume anything about an output
  // argument's initial value — it is undetermined and implementation
  // dependent — the callee never sees the caller's actual on an output
  // formal. This implementation deterministically chooses the formal type's
  // zero as its undetermined seed. `width` is the width the formal's
  // declaration gave it, which is what §35.5.6's packed formals need: the zero
  // of a `bit [127:0]` formal is 128 bits of it, and the kind says only `bit`.
  // Left at 0 the width is the kind's own, which is every formal whose type
  // carries its width.
  static DpiArgValue UndeterminedOutputValue(DataTypeKind type,
                                             uint32_t width = 0);

  // §35.5.1.2: call an import applying input/output/inout argument-passing
  // semantics. `actuals` holds the caller's actual argument values and is
  // updated in place. Input arguments are passed by value: the foreign
  // function sees the actual but any modification it makes is discarded, so
  // the actual is never changed and the change is not visible outside. Inout
  // arguments are seeded with the actual's initial value (which the foreign
  // function can read) and the value written back is visible outside. Output
  // arguments are seeded with an undetermined value rather than the actual,
  // and the value written back is visible outside. Returns the function result.
  DpiArgValue CallImportWithArgs(std::string_view sv_name,
                                 std::vector<DpiArgValue>& actuals) const;

  // §35.6.2: call an import and, once control has returned, detect the value
  // changes on its output and inout actuals and report them as value-change
  // events. The copy-back into the actuals is performed by CallImportWithArgs
  // (§35.5.1.2/§35.6.1) and completes before any event is raised, so detection
  // and handling happen strictly after the imported function returns and never
  // during the call. A value-change event is appended only for an actual the
  // call truly altered, modeling "the actual was assigned the formal
  // immediately after control returns" — an unchanged actual raises none. When
  // there is more than one argument the events are appended in declaration
  // order, the order general SystemVerilog rules impose on the assignments and
  // their value-change propagation. `changes` receives the ordered events; the
  // function result is returned.
  DpiArgValue CallImportDetectingChanges(
      std::string_view sv_name, std::vector<DpiArgValue>& actuals,
      std::vector<DpiArgValueChange>& changes) const;

  DpiArgValue CallExport(std::string_view sv_name,
                         const std::vector<DpiArgValue>& args) const;

  // §35.5.2: whether a SystemVerilog compiler optimization may remove a call to
  // the named import -- true exactly when the import is declared pure. A pure
  // function's call can be eliminated where its result is not needed, and
  // replaced with the value previously computed for the same values of its
  // input arguments. A call to any other import has to be made, §35.5.1.3
  // leaving one declared with neither special property free to have side
  // effects such as writing to a file. A name this runtime holds no declaration
  // for is not removable either.
  bool ImportCallIsRemovable(std::string_view sv_name) const;

  // §35.5.2: calls the named import, or answers with the value a previous call
  // presenting these same input argument values computed. A pure function has
  // no side effects whatsoever and its result depends solely on the values of
  // its input arguments, so the remembered value is the value a fresh call
  // would compute and the foreign function is not entered a second time. An
  // import not declared pure is entered on every call however often it has been
  // called before, and so is a name this runtime holds no declaration for.
  //
  // The import is entered through DpiRtFunction::impl, the form that reads its
  // arguments without writing them, which is the only form a pure function
  // needs: §35.5.2 admits no output or inout formal on one.
  //
  // Only this entry point reuses a result. CallImport and CallImportWithArgs
  // enter the foreign function as they always did, whatever calls have been
  // made here.
  DpiArgValue CallImportReusingPureResult(std::string_view sv_name,
                                          const std::vector<DpiArgValue>& args);

  void PushScope(DpiScope scope);
  void PopScope();
  const DpiScope* CurrentScope() const;
  void SetScope(const DpiScope* scope);
  const DpiScope* GetScope() const;

  // §35.5.3 call-chain instrumentation. A DPI import call chain begins when
  // SystemVerilog calls an import; the chain's context property comes from
  // the import's declaration. EnterContextImportCall/EnterNoncontextImportCall
  // push one frame each; the chain's "is_context" is the property of the
  // root (the bottom-most frame), and per the LRM context is not transitively
  // promoted to subsequent inner import calls. §35.8: is_task records whether
  // the import opening the frame is itself a task (true) or a function (false);
  // a function frame may never call an exported task.
  void EnterContextImportCall(std::string_view sv_name, DpiScope decl_scope,
                              bool is_task = false);
  void EnterNoncontextImportCall(std::string_view sv_name,
                                 bool is_task = false);

  // §35.5.1.3: opens a frame for a call to `sv_name` whose context property is
  // the one that import's own declaration carries, rather than the one the call
  // site names. §35.5.1.3 gives an imported subroutine either the pure property
  // or the context property or neither, and only the context property lets a
  // subroutine reach a SystemVerilog data object other than its actual
  // arguments. So an import declared context opens a context frame scoped to
  // `decl_scope`, and an import declared pure opens a noncontext frame, as does
  // one declared with neither property. A name this runtime holds no
  // declaration for has declared neither, and opens a noncontext frame too.
  // §H.2: whether the frame is a task's is likewise the declaration's, an
  // imported task being the kind that can call exported tasks; a name without
  // a declaration opens a function frame.
  void EnterDeclaredImportCall(std::string_view sv_name, DpiScope decl_scope);

  void LeaveImportCall();
  uint32_t ImportCallDepth() const;
  bool ChainRootIsContext() const;

  // §H.9: a DPI-C context call chain is a sequence of C subroutine
  // invocations that starts with a SystemVerilog entity calling a DPI-C import
  // declared with the context keyword and continues in C, unbroken by a call
  // back into SystemVerilog. A call of an export is such a call back, so the
  // chain ends at it and an import the export's SystemVerilog code then calls
  // starts a chain of its own; when the export returns the chain it broke off
  // from resumes. These read the chain the current point of execution is in:
  // whether there is one, how many are open -- one more per export call whose
  // SystemVerilog code has called an import again -- and whether the current
  // one is a context chain, which is its innermost import being context since
  // §35.5.3 has the property not promoted to an inner call. The behavior of
  // the DPI utility functions that manipulate context is undefined outside a
  // context chain, so this is what a caller of them stands on.
  bool InCallChain() const;
  uint32_t OpenCallChainCount() const;
  bool InContextCallChain() const;

  // §35.5.3: only context import calls (i.e., chains whose root is a context
  // import) can safely invoke a SystemVerilog export subroutine. Returns the
  // outcome and, on kOk, runs the export's registered implementation.
  DpiExportCallStatus CallExportFromImport(std::string_view sv_name,
                                           const std::vector<DpiArgValue>& args,
                                           DpiArgValue* out_result);

  // §35.5.3: reports whether a call to the named import would act as a
  // barrier for SystemVerilog compiler optimizations — true exactly when the
  // import is declared context. Optimizers query this to decide whether the
  // call may be folded or eliminated.
  bool IsImportCallOptimizationBarrier(std::string_view sv_name) const;

  // §35.9 item a) plus the §35.9 carve-out for a directly targeted export.
  // Models an exported task returning while a disable is in effect and yields
  // the int value the task returns — the value SystemVerilog guarantees, not
  // one the DPI application has to ensure. When the disable targets a parent in
  // the chain the task returns 1 and the calling import enters the disabled
  // state; when the exported task is itself the disable target the disable
  // stops there, so the task returns 0 and the parent is not disabled; with no
  // disable the task returns 0. The current thread's disabled state is updated
  // to match.
  int ReturnFromExportUnderDisable(DpiDisableTarget target);

  // Annex H.14: the reference the foreign code receives for the packed data
  // actual at `actual_data` on a call to the import `sv_name`. Under the SV3.1a
  // semantics §H.14 describes this is the address of the simulator's own
  // representation of the array, so no conversion or marshalling happens on
  // either side of the call and a write the foreign code makes through the
  // reference writes the array the caller passed. Under the IEEE Std 1800
  // semantics there is no such reference and the result is nullptr, because
  // packed data reaches the foreign code as the canonical copy §H.10.1.2
  // defines. A name this runtime holds no declaration for is passed its packed
  // data in the canonical representation, which is what a simulator declining
  // §H.14's deprecated functionality provides.
  void* PackedArgRef(std::string_view sv_name, void* actual_data) const;

  // §35.9: whether the current imported subroutine is in the disabled state —
  // the same value svIsDisabledState() reports.
  bool IsDisabledState() const;

  // §35.9 items b) and c): the verification a simulator shall perform on
  // imported subroutines that return while a disable is in effect. Returns true
  // when the protocol was followed and false when it was violated; on a false
  // result the caller issues the fatal simulation error §35.9 mandates. An
  // imported task (item b) shall return 1 when it returns due to a disable; an
  // imported function (item c) shall have called svAckDisabledState() before
  // returning due to a disable. When no disable is in effect there is nothing
  // to verify and the result is true.
  bool CheckImportedSubroutineDisableReturn(bool is_task,
                                            int task_return_value) const;

  // §35.9 items b) and c): verify that the imported subroutine whose call frame
  // is innermost followed the disable protocol on its return, and issue the
  // fatal simulation error §35.9 mandates where it did not. §35.9 makes items
  // b), c) and d) the responsibility of the DPI programmer and requires a
  // simulator to check them, so a violation is reported rather than corrected.
  // `task_return_value` is the int an imported task returns and is ignored when
  // the innermost frame belongs to an imported function. Call this before
  // LeaveImportCall, which pops the frame naming which of the two returned.
  // With no import call open there is no return to verify and the result is
  // true. LeaveImportCall makes the item c) check on its own, because the
  // acknowledgement is thread state the function has either set or not; only
  // item b) needs a value no frame carries.
  bool VerifyImportReturnUnderDisable(int task_return_value);

  // §35.9: whether a fatal simulation error has been issued for a violation of
  // the disable protocol, and the text it carried. §35.9 leaves no discretion
  // here — "if any protocol item is not correctly followed, a fatal simulation
  // error is issued" — so a caller driving this runtime halts the run once this
  // reports true.
  bool DisableProtocolFatalErrorIssued() const;
  const std::string& DisableProtocolFatalError() const;

  static int32_t SvLow(const SvOpenArrayHandle& h);
  static int32_t SvHigh(const SvOpenArrayHandle& h);
  static uint32_t SvSize(const SvOpenArrayHandle& h);

  // §35.6.1.1: under the WYSIWYG principle the unsized ranges of an open-array
  // formal (§35.5.6.1) are not fixed by the import declaration; they are
  // determined at the call site from the corresponding actual argument. These
  // two build the open-array handle a foreign function receives for such a
  // formal, and the clause gives each kind of unsized dimension its own range:
  // the rest of the type information (the element width) stays as specified at
  // the import declaration either way.

  // §35.6.1.1: "A solitary, unsized, packed dimension assumes the linearized,
  // normalized range of the actual's packed dimensions (see H.7.6)."
  // Linearizing "an arbitrary number of sized dimensions" (§35.5.6.1) leaves a
  // count of elements rather than any one declared range, so `actual_bits` is
  // that count and the range the formal takes on is the normalized 0 to
  // actual_bits-1 whatever ranges the actual's own dimensions ran over.
  static SvOpenArrayHandle MakeOpenArrayFromPackedActual(void* actual_data,
                                                         uint32_t actual_bits,
                                                         uint32_t elem_width);

  // §H.7.1: packed arrays can have any number of dimensions but are always
  // equivalent to a one-dimensional packed array and treated as such, so an
  // actual whose packed part is multidimensional is linearized and normalized
  // into the equivalent one-dimensional packed array before an open-array
  // formal takes its range -- the size is the product of the dimensions'
  // sizes and the range the normalized 0 to size-1 of §H.7.5, the original
  // packed ranges not being kept, where an unpacked dimension's are (above).
  // A dimension is counted however its range runs, [7:0] and [0:7] alike.
  static uint32_t LinearizedPackedSize(
      const std::vector<SvActualDimension>& packed_dims);
  static SvOpenArrayHandle MakeOpenArrayFromPackedActual(
      void* actual_data, const std::vector<SvActualDimension>& packed_dims,
      uint32_t elem_width);

  // §35.6.1.1: "A formal's unsized, unpacked dimensions take on the ranges of
  // the corresponding actual dimension." No normalization here: the formal
  // reports the actual dimension's own bounds, so §35.5.6.1's `MyType a_10x5
  // [11:20][6:2]` bound to `MyType i [][]` gives the first formal dimension the
  // range 11 to 20 rather than 0 to 9. The size follows from those bounds,
  // since an unpacked dimension has as many elements as its range has values.
  static SvOpenArrayHandle MakeOpenArrayFromUnpackedActual(
      void* actual_data, SvActualDimension actual, uint32_t elem_width);

 private:
  // §35.9 item b): an imported task returning due to a disable shall return 1.
  // Issues the fatal simulation error and returns false when it returned
  // anything else.
  bool VerifyImportTaskReturnUnderDisable(std::string_view sv_name,
                                          int task_return_value);

  // §35.9 item c): an imported function returning due to a disable shall have
  // called svAckDisabledState() first. Issues the fatal simulation error and
  // returns false when it did not.
  bool VerifyImportFunctionReturnUnderDisable(std::string_view sv_name);

  // §35.9: report and record the fatal simulation error a disable-protocol
  // violation issues.
  void IssueDisableProtocolFatalError(const std::string& message);

  // The status barring a call to the export `exp`, named `sv_name` in
  // SystemVerilog, or kOk where §35.9 item d), §35.8 and §35.5.3 all permit it.
  DpiExportCallStatus CheckExportCallPermitted(const DpiRtExport* exp,
                                               std::string_view sv_name);

  struct ImportFrame {
    std::string_view sv_name;
    bool is_context = false;
    // §35.8: whether the import that opened this frame is a task. A function
    // frame may not call an exported task.
    bool is_task = false;
    // §35.5.3: the chain scope this frame was entered under. A noncontext frame
    // pushes no scope of its own, so it restores this value on leaving rather
    // than popping: §35.5.3 lets a call of an import not specified as context
    // affect its actual arguments and nothing else, which a scope left behind
    // for whatever runs next would breach.
    //
    // entry_scope_from_stack records that the scope at entry was the top of
    // scope_stack_ rather than one svSetScope named, in which case leaving
    // reads the top afresh instead of following this pointer. A PushScope made
    // while the frame ran can move the vector's elements, and the address the
    // top had at entry is not the address it has now.
    const DpiScope* entry_scope = nullptr;
    bool entry_scope_from_stack = false;
  };

  std::vector<DpiRtFunction> imports_;
  std::unordered_map<std::string_view, size_t> import_index_;
  std::vector<DpiRtExport> exports_;
  std::unordered_map<std::string_view, size_t> export_index_;
  // §35.5.3: each export instance under the instantiated scope declaring it and
  // its SystemVerilog name together, so that the instances one exported
  // subroutine has in several scopes stay separately reachable. export_index_
  // keys on the name alone and holds one of them.
  std::unordered_map<std::string, size_t> export_scope_index_;
  // §35.4: the global name space imports and exports share, each linkage name
  // held against the first declaration that resolved to it. A later declaration
  // referring to one global subroutine does not displace the earlier one,
  // because the two name one symbol rather than two. Keying on linkage names is
  // what makes this a different name space from the SystemVerilog names
  // import_index_ and export_index_ are keyed by.
  std::unordered_map<std::string_view, size_t> import_global_index_;
  std::unordered_map<std::string_view, size_t> export_global_index_;
  // §35.5.2: the value each pure import call computed, kept under the import's
  // name and the values its input arguments presented, so that a later call
  // presenting the same values can be answered from it.
  std::unordered_map<std::string, DpiArgValue> pure_results_;
  // §H.9.3: the scopes pushed by the context import frames, each the handle
  // the §H.9.3 registry holds for its name, so that the scope svGetScope
  // reports inside a chain is the one svGetScopeFromName reports for the
  // instance and user data stored under either is found under the other --
  // §H.9.4's example stores a model under the handle a name resolves to and
  // retrieves it under the scope the executing import reports. A pushed scope
  // with no name, which a run that does not yet carry instantiated scopes
  // pushes, is held in unnamed_scopes_ for the length of its frame instead.
  std::vector<const DpiScope*> scope_stack_;
  std::deque<DpiScope> unnamed_scopes_;
  const DpiScope* current_scope_ = nullptr;
  std::vector<ImportFrame> call_chain_;
  // §H.9: the index in call_chain_ at which each open chain starts. The first
  // chain starts at 0; an export call that has called back into SystemVerilog
  // pushes the index the next import frame will take, and pops it when the
  // export returns.
  std::vector<size_t> chain_starts_;
  // §35.9: whether a disable-protocol violation has issued its fatal simulation
  // error, and the message of the first one, which is the error that ends the
  // run.
  bool disable_protocol_fatal_ = false;
  std::string disable_protocol_fatal_message_;
};

// §35.5.3: "the current scope" decides which instance of an exported subroutine
// a call reaches, so the C layer and the run have to answer that question the
// same way. The run's registry is installed here -- by
// SimContext::AcquireDpiRuntime and SimContext::SetDpiRuntime -- and the §H.9.3
// entry points svGetScope() and svSetScope() read and write its scope through
// it rather than a second copy of the state.
//
// It is a free function beside the disable state above for the reason that one
// is: §H.9.3 gives a foreign routine no handle to pass, so the run's registry
// has to be reachable without one. Null where no run has installed one, which
// is what a translation unit exercising the value utilities on their own
// leaves it at, and what a run's context restores when it goes away.
void DpiSetForeignRuntime(DpiRuntime* runtime);
DpiRuntime* DpiForeignRuntime();

}  // namespace delta
