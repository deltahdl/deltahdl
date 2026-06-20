#pragma once

#include <cstdarg>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"
#include "simulator/coverage_control.h"

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

// §38.35: the additional value formats vpi_put_value_array() accepts on top of
// the vpi_get_value() formats of §38.15 (Table 38-3). The raw forms carry an
// element's aval/bval bytes directly; the int/long/real forms carry one C
// scalar per element.
constexpr int kVpiShortIntVal = 14;
constexpr int kVpiLongIntVal = 15;
constexpr int kVpiShortRealVal = 16;
constexpr int kVpiRawTwoStateVal = 17;
constexpr int kVpiRawFourStateVal = 18;

// §38.35: the only flags vpi_put_value_array() permits. vpiOneValue applies a
// single supplied element value to the whole selected section; vpiPropagateOff
// suppresses fanout notification; vpiNoDelay (the default, value 0 in the flags
// word) is the only scheduling mode the routine allows.
constexpr int kVpiOneValue = 0x4000;
constexpr int kVpiPropagateOff = 0x8000;

// §38.16: with vpiUserAllocFlag set in arrayvalue.flags, vpi_get_value_array()
// writes the retrieved values into a buffer the application has already pointed
// the value arm at, instead of allocating VPI-owned storage for them.
constexpr int kVpiUserAllocFlag = 0x2000;

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

// §37.3.7: the three (and only three) allocation schemes
// vpi_get(vpiAllocScheme) may return. These live in the property-RETURN-value
// namespace, distinct from the selector numbers above, so small contiguous ints
// are unambiguous.
//   kVpiAutomaticScheme -> object lives with a frame or thread
//   kVpiDynamicScheme   -> object was allocated in dynamic memory (e.g. a
//   class) kVpiOtherScheme     -> the mandated default for every other object
constexpr int kVpiAutomaticScheme = 1;
constexpr int kVpiDynamicScheme = 2;
constexpr int kVpiOtherScheme = 3;

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

}  // namespace delta
