#pragma once

#include <cstdint>

namespace delta {

void DpiGetSimTime(bool want_scaled_real, uint32_t* high, uint32_t* low,
                   double* real);
int32_t DpiGetSimTimeUnit();
int32_t DpiGetSimTimePrecision();
double DpiGetSimTimeScaledTo(int32_t time_unit);

}  // namespace delta
