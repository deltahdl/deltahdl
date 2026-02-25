// Annex H.13: Time and timescale

#include <gtest/gtest.h>

#include "vpi/svdpi.h"

namespace {

TEST(SvDpi, TimeValAlias) {
  svTimeVal tv;
  tv.type = sv_sim_time;
  tv.high = 0;
  tv.low = 100;
  tv.real = 0.0;
  EXPECT_EQ(tv.type, vpiSimTime);
}

TEST(SvDpi, TimeConstants) {
  EXPECT_EQ(sv_scaled_real_time, vpiScaledRealTime);
  EXPECT_EQ(sv_sim_time, vpiSimTime);
}

}  // namespace
