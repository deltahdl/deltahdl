#pragma once

#include <cstdint>
#include <vector>

#include "simulator/vpi_constants.h"
#include "simulator/vpi_object.h"

namespace delta {

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

// §38.35 (s_vpi_arrayvalue): the aggregate that carries the values
// vpi_put_value_array() writes into a static unpacked array. format selects
// which arm of the union is live and how each element is encoded; flags carries
// vpiOneValue/vpiPropagateOff. Every arm is a pointer to caller-allocated
// storage holding one entry per element (the raw arms hold packed aval/bval
// bytes instead). The public spellings s_vpi_arrayvalue/p_vpi_arrayvalue alias
// this type below.
struct VpiArrayValue {
  uint32_t format = 0;
  uint32_t flags = 0;
  union {
    int32_t* integers;
    int16_t* shortints;
    int64_t* longints;
    char* rawvals;
    VpiVectorVal* vectors;
    VpiTime* times;
    double* reals;
    float* shortreals;
  } value = {};
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
  // §38.36 (Figure 38-17): the application routine the simulator invokes when
  // it executes the callback; it is passed a pointer to this s_cb_data
  // structure.
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
int VpiSystfReturnType(const VpiSystfData& data);

// §38.37.1: whether a given callback application fires while the simulation
// data structure is being compiled or built (true for compiletf and sizetf)
// rather than on every invocation during simulation execution (false for
// calltf).
bool VpiSystfCallbackFiresAtBuild(VpiSystfCallback callback);

// §38.37.1: invoke one of the systf callback applications. Every callback
// receives exactly one argument - the registration's user_data field, passed as
// a PLI_BYTE8 * - and a null function pointer (a field left unused) is simply
// skipped, returning 0.
int VpiSystfInvoke(int (*routine)(const char*), void* user_data);

// §38.37.1 (sizetf rule): whether the sizetf application is to be called for a
// registration. It is called only for a system function (vpiSysFunc) whose
// sysfunctype is vpiSizedFunc or vpiSizedSignedFunc; for anything else sizetf
// is never invoked.
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
