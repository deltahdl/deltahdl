#pragma once

#include <cstdarg>

#include "simulator/vpi_user.h"

namespace delta {

class SimContext;
class Scheduler;
class Arena;
struct Net;
struct Process;
struct Variable;

constexpr int kVpiModule = vpiModule;
constexpr int kVpiNet = vpiNet;
constexpr int kVpiReg = vpiReg;
constexpr int kVpiPort = vpiPort;
constexpr int kVpiParameter = vpiParameter;
constexpr int kVpiCallback = vpiCallback;

// §38.13: a time queue object stands in for the simulator's pending-event
// queue. vpi_get_time() treats it specially, reporting the scheduled time of
// the next future event rather than the current simulation time.
constexpr int kVpiTimeQueue = vpiTimeQueue;

constexpr int kVpiBinStrVal = vpiBinStrVal;
constexpr int kVpiOctStrVal = vpiOctStrVal;
constexpr int kVpiHexStrVal = vpiHexStrVal;
constexpr int kVpiScalarVal = vpiScalarVal;
constexpr int kVpiIntVal = vpiIntVal;
constexpr int kVpiRealVal = vpiRealVal;
constexpr int kVpiStringVal = vpiStringVal;
constexpr int kVpiTimeVal = vpiTimeVal;
constexpr int kVpiVectorVal = vpiVectorVal;
constexpr int kVpiStrengthVal = vpiStrengthVal;
constexpr int kVpiObjTypeVal = vpiObjTypeVal;

// §38.35: the additional value formats vpi_put_value_array() accepts on top of
// the vpi_get_value() formats of §38.15 (Table 38-3). The raw forms carry an
// element's aval/bval bytes directly; the int/long/real forms carry one C
// scalar per element.
constexpr int kVpiShortIntVal = vpiShortIntVal;
constexpr int kVpiLongIntVal = vpiLongIntVal;
constexpr int kVpiShortRealVal = vpiShortRealVal;
constexpr int kVpiRawTwoStateVal = vpiRawTwoStateVal;
constexpr int kVpiRawFourStateVal = vpiRawFourStateVal;

// §38.35: the only flags vpi_put_value_array() permits. vpiOneValue applies a
// single supplied element value to the whole selected section; vpiPropagateOff
// suppresses fanout notification; vpiNoDelay (the default, value 0 in the flags
// word) is the only scheduling mode the routine allows.
constexpr int kVpiOneValue = vpiOneValue;
constexpr int kVpiPropagateOff = vpiPropagateOff;

// §38.16: with vpiUserAllocFlag set in arrayvalue.flags, vpi_get_value_array()
// writes the retrieved values into a buffer the application has already pointed
// the value arm at, instead of allocating VPI-owned storage for them.
constexpr int kVpiUserAllocFlag = vpiUserAllocFlag;

constexpr int kVpiSimTime = vpiSimTime;
constexpr int kVpiScaledRealTime = vpiScaledRealTime;

constexpr int kCbValueChange = cbValueChange;
constexpr int kCbReadWriteSynch = cbReadWriteSynch;
constexpr int kCbEndOfSimulation = cbEndOfSimulation;
constexpr int kCbStmt = cbStmt;
constexpr int kCbAtStartOfSimTime = cbAtStartOfSimTime;
constexpr int kCbReadOnlySynch = cbReadOnlySynch;

constexpr int kCbAfterDelay = cbAfterDelay;
constexpr int kCbNextSimTime = cbNextSimTime;
constexpr int kCbNBASynch = cbNBASynch;
constexpr int kCbAtEndOfSimTime = cbAtEndOfSimTime;

// §38.36.3: simulator action callbacks name reasons that every VPI-compliant
// tool provides (kCbEndOfSimulation above is also an action reason); simulator
// feature callbacks name optional, tool-specific reasons such as save, restart,
// reset, and interactive-mode transitions. They are registered through the same
// vpi_register_cb() path as every other callback reason.
constexpr int kCbEndOfCompile = cbEndOfCompile;
constexpr int kCbStartOfSimulation = cbStartOfSimulation;
constexpr int kCbError = cbError;
constexpr int kCbPLIError = cbPLIError;
constexpr int kCbTchkViolation = cbTchkViolation;
constexpr int kCbSignal = cbSignal;
constexpr int kCbStartOfSave = cbStartOfSave;
constexpr int kCbEndOfSave = cbEndOfSave;
constexpr int kCbStartOfRestart = cbStartOfRestart;
constexpr int kCbEndOfRestart = cbEndOfRestart;
constexpr int kCbStartOfReset = cbStartOfReset;
constexpr int kCbEndOfReset = cbEndOfReset;
constexpr int kCbEnterInteractive = cbEnterInteractive;
constexpr int kCbExitInteractive = cbExitInteractive;
constexpr int kCbInteractiveScopeChange = cbInteractiveScopeChange;
constexpr int kCbUnresolvedSystf = cbUnresolvedSystf;

constexpr int kVpiType = vpiType;
constexpr int kVpiName = vpiName;
constexpr int kVpiFullName = vpiFullName;
constexpr int kVpiSize = vpiSize;
constexpr int kVpiDirection = vpiDirection;
constexpr int kVpiDefName = vpiDefName;

// §37.3.7: vpiAutomatic is the standard Boolean lifetime selector (the same
// value 50 already used elsewhere in this header). It is repeated here as a
// kVpi* constant so the Get() switch can read an object's declared lifetime in
// the same idiom as the other property selectors.
constexpr int kVpiAutomatic = vpiAutomatic;

// §37.3.7: vpiAllocScheme is the enumeration property naming how an object's
// memory was obtained. 658 is the number Annex M gives it in sv_vpi_user.h,
// which this constant mirrors as the other kVpi constants mirror theirs.
constexpr int kVpiAllocScheme = vpiAllocScheme;

// §37.3.7: the three (and only three) allocation schemes
// vpi_get(vpiAllocScheme) may return. These live in the property-RETURN-value
// namespace, distinct from the selector numbers above, so small contiguous ints
// are unambiguous.
//   kVpiAutomaticScheme -> object lives with a frame or thread
//   kVpiDynamicScheme   -> object was allocated in dynamic memory (e.g. a
//   class) kVpiOtherScheme     -> the mandated default for every other object
constexpr int kVpiAutomaticScheme = vpiAutomaticScheme;
constexpr int kVpiDynamicScheme = vpiDynamicScheme;
constexpr int kVpiOtherScheme = vpiOtherScheme;

// §37.61 detail 3: how a dynamically prefixed object's correspondence to an
// actual is established, which fixes what vpiHasActual reports. These live in a
// private namespace (not VPI selector values) describing the provenance the
// clause enumerates, not anything queried directly.
//   kVpiActualBySimTime    -> depends on whether a corresponding actual exists
//                             at the current simulation time (the default case)
//   kVpiActualStaticElab   -> all or part of a statically declared object in an
//                             elaborated context (always has an actual)
//   kVpiActualFrameVar     -> automatically allocated variable from a frame,
//                             see §37.43 (always has an actual)
//   kVpiActualLexicalDefn  -> obtained from a lexical context such as a class
//                             defn, see §37.31 (never has an actual)
//   kVpiActualClassTypespec-> part of a non-static class property referenced
//                             relative to its class typespec, see §37.32 (none)
//   kVpiActualTaskFuncVar  -> automatically allocated variable from a task or
//                             function declaration, see §37.41 (none)
constexpr int kVpiActualBySimTime = 0;
constexpr int kVpiActualStaticElab = 1;
constexpr int kVpiActualFrameVar = 2;
constexpr int kVpiActualLexicalDefn = 3;
constexpr int kVpiActualClassTypespec = 4;
constexpr int kVpiActualTaskFuncVar = 5;

constexpr int kVpiLibrary = vpiLibrary;
constexpr int kVpiConfig = vpiConfig;
constexpr int kVpiCell = vpiCell;

constexpr int kVpiInput = vpiInput;
constexpr int kVpiOutput = vpiOutput;
constexpr int kVpiInout = vpiInout;

constexpr int kVpiNoDelay = vpiNoDelay;
constexpr int kVpiInertialDelay = vpiInertialDelay;
constexpr int kVpiTransportDelay = vpiTransportDelay;
constexpr int kVpiPureTransportDelay = vpiPureTransportDelay;

constexpr int kVpiFinish = vpiFinish;
constexpr int kVpiStop = vpiStop;
// §38.36.3: a reset can be requested indirectly through vpi_control(vpiReset).
constexpr int kVpiReset = vpiReset;
// §38.4: vpi_control(vpiSetInteractiveScope, handle) immediately retargets the
// tool's interactive scope to the supplied vpiScope object.
constexpr int kVpiSetInteractiveScope = vpiSetInteractiveScope;

constexpr int kVpi0 = vpi0;
constexpr int kVpi1 = vpi1;
constexpr int kVpiX = vpiX;
constexpr int kVpiZ = vpiZ;

// §38.2 Table 38-1: the vpi_chk_error() severity levels, ordered from lowest
// (vpiNotice) to highest (vpiInternal). The values increase with severity, so
// vpiSystem outranks vpiError and vpiInternal outranks them all.
constexpr int kVpiNotice = vpiNotice;
constexpr int kVpiWarning = vpiWarning;
constexpr int kVpiError = vpiError;
constexpr int kVpiSystem = vpiSystem;
constexpr int kVpiInternal = vpiInternal;

// §38.2 (Figure 38-1): the s_vpi_error_info state field, "vpi[Compile,PLI,Run]"
// -- what the tool was doing when the error occurred, and not how bad it was.
// The severity is the level field above, and the two are numbered
// independently, so a state carrying a level's constant reads as one of these
// three by accident: kVpiError is the value vpiRun has and kVpiWarning the
// value vpiPLI has. An error a VPI routine itself raises is kVpiPLI, that being
// what the routine was doing; kVpiCompile and kVpiRun name the other two
// activities an error can arise in.
// §38.9: the save/restart location this run keeps its saved data in, as
// vpi_get(vpiSaveRestartID, NULL) hands it back -- "a save/restart ID returned
// from vpi_get(vpiSaveRestartID, NULL)" is where the clause has an application
// get the id it then passes to vpi_put_data() and vpi_get_data(). A run has one
// such location, so it has one id, and the value is nonzero because zero is
// what vpi_get() answers for a property it does not have.
constexpr int kVpiRunSaveRestartId = 1;

constexpr int kVpiCompile = vpiCompile;
constexpr int kVpiPLI = vpiPLI;
constexpr int kVpiRun = vpiRun;

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

}  // namespace delta
