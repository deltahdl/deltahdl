#pragma once

#include "common/types.h"

namespace delta {

class VpiContext;

Region RegionForPliCallback(int reason);

bool IsOneShotPliCallback(int reason);

VpiContext& GetGlobalVpiContext();
void SetGlobalVpiContext(VpiContext* ctx);

using VlogStartupRoutine = void (*)();

void InvokeVlogStartupRoutines(VlogStartupRoutine* routines);

}  // namespace delta

extern "C" delta::VlogStartupRoutine vlog_startup_routines[];
