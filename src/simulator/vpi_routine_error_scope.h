#pragma once

#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"

namespace delta {

// The error status of one VPI routine call, from end to end. §38.2 has every
// VPI routine but vpi_chk_error() reset the error status, which is what the
// constructor does, and §36.10.1 lets callbacks be placed on an error
// occurring, which is what the destructor delivers: an error this routine
// recorded is the occurrence those callbacks are registered for, and it has
// occurred by the time the routine is done recording it.
//
// One object per routine rather than a call at each of the sites that record an
// error, because what a routine reports is the error status it leaves behind
// and not each write on the way there: a routine that records one error and
// then replaces it has had one error occur in it. Every entry point an
// application calls opens one: those of vpi.cpp, the compatibility-mode names
// of vpi_compatibility.cpp, and the assertion API's of sv_vpi_user.cpp.
class VpiRoutineErrorScope {
 public:
  VpiRoutineErrorScope() { GetGlobalVpiContext().ResetErrorStatus(); }
  ~VpiRoutineErrorScope() { GetGlobalVpiContext().NoteErrorRecorded(); }

  VpiRoutineErrorScope(const VpiRoutineErrorScope&) = delete;
  VpiRoutineErrorScope& operator=(const VpiRoutineErrorScope&) = delete;
};

}  // namespace delta
