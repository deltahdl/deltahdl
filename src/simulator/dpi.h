#pragma once

#include <cstdint>

namespace delta {

// §H.13 bridge between the DPI C layer and the simulator's time state. The DPI
// time routines svGetTime/svGetTimeUnit/svGetTimePrecision (svdpi.cpp) report
// the same simulation time the VPI time routines do, but svdpi.cpp cannot pull
// in the VPI headers (their time constants and s_vpi_time spelling collide with
// svdpi.h's own). These accessors expose the design-wide time state as plain
// integers so the DPI layer stays free of those headers; the implementation
// lives in vpi.cpp where the VPI context is in scope.
//
// Report the current simulation time for the design as a whole (the time a NULL
// svScope selects). When want_scaled_real is true the time scaled to the
// simulation time unit is written to *real; otherwise the 64-bit
// simulation-time count is split into *high/*low. Equivalent to vpi_get_time()
// with a null object.
void DpiGetSimTime(bool want_scaled_real, uint32_t* high, uint32_t* low,
                   double* real);
// The design-wide simulation time unit and precision, equivalent to the values
// vpi_get() yields for vpiTimeUnit and vpiTimePrecision with a null object.
int32_t DpiGetSimTimeUnit();
int32_t DpiGetSimTimePrecision();

}  // namespace delta
