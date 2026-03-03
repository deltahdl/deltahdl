// Non-LRM tests

#include <gtest/gtest.h>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulator/clocking.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(Clocking, OutputSkew) {
  ClockingManager mgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.default_input_skew = SimTime{1};
  block.default_output_skew = SimTime{3};
  mgr.Register(block);

  auto skew = mgr.GetOutputSkew("cb", "data_out");
  EXPECT_EQ(skew.ticks, 3u);
}

}  // namespace
