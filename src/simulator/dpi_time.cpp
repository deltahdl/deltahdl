#include <cmath>
#include <cstdint>

#include "simulator/dpi.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_user.h"

namespace delta {

void DpiGetSimTime(bool want_scaled_real, uint32_t* high, uint32_t* low,
                   double* real) {
  s_vpi_time t = {};
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
  s_vpi_time t = {};
  t.type = kVpiSimTime;
  GetGlobalVpiContext().GetTime(nullptr, &t);
  const uint64_t kTicks = (static_cast<uint64_t>(t.high) << 32) | t.low;
  const double kScale = std::pow(
      10.0,
      static_cast<double>(GetGlobalVpiContext().SimTimeUnit() - time_unit));
  return static_cast<double>(kTicks) * kScale;
}

}  // namespace delta
