#pragma once

#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"

namespace delta {

class VpiRoutineErrorScope {
 public:
  VpiRoutineErrorScope() { GetGlobalVpiContext().ResetErrorStatus(); }
  ~VpiRoutineErrorScope() { GetGlobalVpiContext().NoteErrorRecorded(); }

  VpiRoutineErrorScope(const VpiRoutineErrorScope&) = delete;
  VpiRoutineErrorScope& operator=(const VpiRoutineErrorScope&) = delete;
};

}  // namespace delta
