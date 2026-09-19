#pragma once

#include <cstdint>

#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

constexpr int kVpiSysTask = vpiSysTask;
constexpr int kVpiSysFunc = vpiSysFunc;

// §38.37.1: the value kinds a system function may declare through the
// sysfunctype field. Only one of these may be named, and only when the system
// task/function was registered as a vpiSysFunc.
constexpr int kVpiIntFunc = vpiIntFunc;
constexpr int kVpiRealFunc = vpiRealFunc;
constexpr int kVpiTimeFunc = vpiTimeFunc;
constexpr int kVpiSizedFunc = vpiSizedFunc;
constexpr int kVpiSizedSignedFunc = vpiSizedSignedFunc;

// §38.37.1: a sized system function (vpiSizedFunc/vpiSizedSignedFunc) whose
// registration supplies no sizetf application returns a value 32 bits wide.
constexpr int kVpiDefaultSizedFuncBits = 32;

// §38.37.1: the three points in the tool's lifetime that drive the callback
// applications named in a s_vpi_systf_data record.
enum class VpiSystfCallback : std::uint8_t { kCompiletf, kSizetf, kCalltf };

// §38.37.1 (tfname rule): whether a candidate system task/function name is a
// well-formed name as it would be written in SystemVerilog source - it begins
// with a dollar sign and is followed by one or more characters that are legal
// in a SystemVerilog simple identifier (A-Z, a-z, 0-9, underscore, dollar
// sign). A bare "$", an empty string, or any other character makes the name
// ill-formed.
bool VpiSystfNameIsValid(const char* tfname);

// §38.37.1 (sysfunctype rule): the value kind a registration declares for a
// system function. sysfunctype is meaningful only when the record was
// registered as a vpiSysFunc; for a system task it does not apply, so this
// reports 0 (no return-value kind) regardless of the stored field.
int VpiSystfReturnType(const s_vpi_systf_data& data);

// §38.37.1: whether a given callback application fires while the simulation
// data structure is being compiled or built (true for compiletf and sizetf)
// rather than on every invocation during simulation execution (false for
// calltf).
bool VpiSystfCallbackFiresAtBuild(VpiSystfCallback callback);

// §38.37.1: invoke one of the systf callback applications. Every callback
// receives exactly one argument - the registration's user_data field, passed as
// a PLI_BYTE8 * - and a null function pointer (a field left unused) is simply
// skipped, returning 0.
int VpiSystfInvoke(PLI_INT32 (*routine)(PLI_BYTE8*), PLI_BYTE8* user_data);

// §38.37.1 (sizetf rule): whether the sizetf application is to be called for a
// registration. It is called only for a system function (vpiSysFunc) whose
// sysfunctype is vpiSizedFunc or vpiSizedSignedFunc; for anything else sizetf
// is never invoked.
bool VpiSystfSizetfIsCalled(const s_vpi_systf_data& data);

// §38.37.1: the bit width a sized system function reports. When sizetf is to be
// called and a sizetf application is present it supplies the width (receiving
// user_data as its PLI_BYTE8 * argument); a sized function with no sizetf
// defaults to 32 bits.
int VpiSystfResultSizeBits(const s_vpi_systf_data& data);

// §36.10.2: the tool-lifecycle phases that gate which VPI routines a PLI
// application may call. kStartup is the window in which the
// vlog_startup_routines[] array executes and very little functionality is
// available; kSizetf is the phase immediately after, when the sizetf routines
// run for user-defined system functions and no access beyond the startup phase
// is permitted; kFull begins once the cbEndOfCompile callbacks are called, from
// which point until the tool finishes all functionality is available.
enum class VpiToolPhase : std::uint8_t { kStartup, kSizetf, kFull };

// §36.10.2: whether a phase restricts VPI functionality. The startup phase and
// the sizetf phase that follows it both restrict it (the sizetf phase permits
// no access beyond the startup phase); only the full phase makes all
// functionality available.
bool VpiPhaseRestrictsFunctionality(VpiToolPhase phase);

// §36.10.2: the VPI routines whose availability the startup-phase restriction
// distinguishes. The two registration routines are the only ones callable while
// the vlog_startup_routines[] array executes; the others stand in for the bulk
// of the interface that is unavailable until the full phase.
enum class VpiRoutine : std::uint8_t {
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

// §38.36.2: whether a callback reason is one of the simulation-time reasons -
// cbAtStartOfSimTime, cbNBASynch, cbReadWriteSynch, cbAtEndOfSimTime,
// cbReadOnlySynch, cbNextSimTime, or cbAfterDelay. These are the reasons whose
// placement vpi_register_cb() constrains through the s_cb_data time structure.
bool VpiIsSimulationTimeCallbackReason(int reason);

// §38.19: whether an object type carries the "access by index" property - the
// property the reference object of vpi_handle_by_index() must have. An object
// has it when one of its relationships selects a sub-object by an index number:
// a module indexes its ports, a net or reg indexes its bits, and an array or
// memory indexes its elements or words. An object type without the property
// cannot anchor a SystemVerilog index select, so it cannot serve as the
// reference object.
bool VpiHasAccessByIndex(int type);

// §37.85 detail 1: the size of a gen scope array - the number of gen scope
// elements it holds - reported through vpi_get(vpiSize). It is counted from the
// array's element children rather than read from a stored width.
int VpiGenScopeArraySize(VpiHandle gen_scope_array);

// §37.81: one entry of the simulation time queue - a simulation time, expressed
// in ticks of the simulation time unit, at which events are still scheduled.
// `is_current` marks the entry at the current simulation time; detail 3 admits
// that entry to the vpi_iterate(vpiTimeQueue, NULL) walk only when events
// remain scheduled before its read-only synch region, recorded by
// `has_events_before_read_only_synch`. A future entry (is_current false) always
// takes part in the iteration.
struct VpiTimeQueueSlot {
  uint64_t time = 0;
  bool is_current = false;
  bool has_events_before_read_only_synch = false;
};

}  // namespace delta
