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
