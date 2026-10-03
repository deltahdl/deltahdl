#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, ThreeMagnitudes) {
  TimeScale ts1{TimeUnit::kNs, 1, TimeUnit::kPs, 1};
  TimeScale ts10{TimeUnit::kNs, 10, TimeUnit::kPs, 1};
  TimeScale ts100{TimeUnit::kNs, 100, TimeUnit::kPs, 1};
  EXPECT_EQ(DelayToTicks(1, ts1, TimeUnit::kPs), 1000u);
  EXPECT_EQ(DelayToTicks(1, ts10, TimeUnit::kPs), 10000u);
  EXPECT_EQ(DelayToTicks(1, ts100, TimeUnit::kPs), 100000u);
}

// §3.14.2.3 leaves a compilation-unit scope without a timeunit at the default
// 1 ns / 1 ns, and §3.14.3 forms the global precision without that default, so
// under `timescale 1us / 1us such a scope's unit is finer than the global
// precision. 3000 ns is three ticks of 1 us, as an integer and as a real.
TEST(DesignBuildingBlockSimulation, UnitFinerThanGlobalPrecisionDividesDown) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kNs, 1};
  EXPECT_EQ(DelayToTicks(3000, ts, TimeUnit::kUs), 3u);
  EXPECT_EQ(RealDelayToTicks(3000.0, ts, TimeUnit::kUs), 3u);
}

TEST(DesignBuildingBlockSimulation, StepTimeUnitTracksLatestGlobalPrecision) {
  SimFixture f;
  f.ctx.SetGlobalPrecision(TimeUnit::kNs);
  ASSERT_EQ(f.ctx.StepTimeUnit(), TimeUnit::kNs);
  EXPECT_EQ(f.ctx.StepTimeUnit(), f.ctx.GlobalPrecision());
  f.ctx.SetGlobalPrecision(TimeUnit::kFs);
  EXPECT_EQ(f.ctx.StepTimeUnit(), TimeUnit::kFs);
  EXPECT_EQ(f.ctx.StepTimeUnit(), f.ctx.GlobalPrecision());
}

// §3.14.3 takes the smallest precision of every `timescale in the design, not
// only the last one: the 1 fs before p makes the global precision 1 fs, so the
// #1.5 of p's task stays 1.5 ns and t reads 1.500. Counted in ticks of the last
// directive's 1 ns, the delay landed on 2 ns.
TEST(DesignBuildingBlockSimulation,
     EarlierFinerTimescaleSetsTheGlobalPrecision) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1ns / 1fs\n"
                                 "package p;\n"
                                 "  task automatic wait_frac(); #1.5; endtask\n"
                                 "endpackage\n"
                                 "`timescale 1ns / 1ns\n"
                                 "module t;\n"
                                 "  initial begin\n"
                                 "    p::wait_frac();\n"
                                 "    $display(\"%0.3f\", $realtime);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f),
            "1.500\n");
}

}  // namespace
