#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_path_delay_run.h"

using namespace delta;

namespace {

TEST(PathDelayValueRun, ModuleBodySpecparamSuppliesTheDelay) {
  EXPECT_EQ(BufferPathRun("  specparam tb = 7;\n", "", "tb", DelayMode::kTyp),
            "70 71 70 \n");
}

TEST(PathDelayValueRun, BareSixValuesTimeTransitionsAsParenthesized) {
  EXPECT_EQ(PathTransitionRun("5, 12, 17, 10, 6, 22"),
            "220 51 120 17z 101 6z 220 5x 101 6x 220 5x 17z 10x \n");
}

TEST(PathDelayValueRun, BareThreePlainValuesTimeRiseAndFall) {
  EXPECT_EQ(BufferPathRun("", "", "1, 2, 3", DelayMode::kTyp), "20 11 20 \n");
}

}  // namespace
