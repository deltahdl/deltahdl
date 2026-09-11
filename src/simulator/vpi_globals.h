#pragma once

// The VPI declarations that stand beside the context rather than inside it: the
// process-wide context a PLI application's calls are answered out of, the two
// callback classifications the scheduler reads, and §36.9.1's startup array.
//
// They live here rather than in simulator/vpi_context.h because that file is
// one class declaration and had reached the 949 lines
// assert-no-oversized-source-files leaves a file, so a declaration could
// neither be added to it nor documented in it. It includes this file, so every
// translation unit that reached these names through it still does.

#include "common/types.h"

namespace delta {

class VpiContext;

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

}  // namespace delta

// §38.37.2: the vlog_startup_routines array the tool supplies, defined in
// src/simulator/vlog_startup_routines.cpp, which is also where the vendor
// definitions §38.37.2 asks for - the array's location and the procedure for
// linking it with the tool - are written down. It is declared here so that the
// walk just after the simulator is invoked, and a test of what the tool ships,
// reach the same array a PLI application adds its register functions to.
//
// The declaration stands outside namespace delta because the name is the one
// §38.37.2 fixes for a C function array: extern "C" gives the symbol C linkage
// wherever it is written, and writing it at namespace scope would say a PLI
// application reaches it as delta::vlog_startup_routines, which it does not.
extern "C" delta::VlogStartupRoutine vlog_startup_routines[];
