#include <gtest/gtest.h>

#include "helpers_delay_mode_directive_vpi.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

TEST_F(DelayModeOfAnInstance, DelayModeZero_ReportedForAChildAfterIt) {
  EXPECT_EQ(DefDelayModeOfAChildAfter("delay_mode_zero"), vpiDelayModeZero);
}

}  // namespace
