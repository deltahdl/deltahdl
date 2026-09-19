// §H.13 time bridge for the DPI C layer, declared in dpi.h and read by the
// svGetTime, svGetTimeUnit and svGetTimePrecision functions of svdpi.cpp. It
// stands in a translation unit of its own so that the VPI headers it reads
// stay out of svdpi.cpp, whose svdpi.h lays down its own s_vpi_time.
#include <cmath>
#include <cstdint>

#include "simulator/dpi.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_user.h"

namespace delta {

// §H.13 time bridge for the DPI C layer (declared in dpi.h). Each accessor
// reads the design-wide time state through the global VPI context, so the DPI
// svGetTime/svGetTimeUnit/svGetTimePrecision functions deliver the very values
// VPI's vpi_get_time()/vpi_get(vpiTimeUnit/vpiTimePrecision) deliver for a null
// object. The VPI time constants are used here, inside the VPI translation
// unit, keeping the VPI headers out of svdpi.cpp.
void DpiGetSimTime(bool want_scaled_real, uint32_t* high, uint32_t* low,
                   double* real) {
  VpiTime t = {};
  // GetTime selects the result form from t.type: a scaled real, or the raw
  // 64-bit simulation-time count. A null object means "the whole design", which
  // GetTime reads in the simulation time unit.
  t.type = want_scaled_real ? kVpiScaledRealTime : kVpiSimTime;
  GetGlobalVpiContext().GetTime(nullptr, &t);
  if (high) *high = t.high;
  if (low) *low = t.low;
  if (real) *real = t.real;
}

int32_t DpiGetSimTimeUnit() {
  return static_cast<int32_t>(GetGlobalVpiContext().Get(vpiTimeUnit, nullptr));
}

int32_t DpiGetSimTimePrecision() {
  return static_cast<int32_t>(
      GetGlobalVpiContext().Get(vpiTimePrecision, nullptr));
}

double DpiGetSimTimeScaledTo(int32_t time_unit) {
  // §H.13 with §38.13: the count the scheduler keeps is in the simulation time
  // unit, and the exponent difference to the requested unit is the power of
  // ten between the two -- the rule VpiContext::GetTime applies to an object
  // read in its own timescale.
  VpiTime t = {};
  t.type = kVpiSimTime;
  GetGlobalVpiContext().GetTime(nullptr, &t);
  const uint64_t kTicks = (static_cast<uint64_t>(t.high) << 32) | t.low;
  const double kScale = std::pow(
      10.0,
      static_cast<double>(GetGlobalVpiContext().SimTimeUnit() - time_unit));
  return static_cast<double>(kTicks) * kScale;
}

}  // namespace delta
