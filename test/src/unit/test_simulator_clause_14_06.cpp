#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ClockingSim, MultipleClockingBlocks) {
  ClockingManager cmgr;

  ClockingBlock block1;
  block1.name = "cb_fast";
  block1.clock_signal = "clk_fast";
  block1.clock_edge = Edge::kPosedge;
  block1.default_input_skew = SimTime{1};
  block1.default_output_skew = SimTime{1};
  cmgr.Register(block1);

  ClockingBlock block2;
  block2.name = "cb_slow";
  block2.clock_signal = "clk_slow";
  block2.clock_edge = Edge::kNegedge;
  block2.default_input_skew = SimTime{5};
  block2.default_output_skew = SimTime{5};
  cmgr.Register(block2);

  EXPECT_EQ(cmgr.Count(), 2u);
  EXPECT_NE(cmgr.Find("cb_fast"), nullptr);
  EXPECT_NE(cmgr.Find("cb_slow"), nullptr);
  EXPECT_EQ(cmgr.Find("cb_fast")->clock_edge, Edge::kPosedge);
  EXPECT_EQ(cmgr.Find("cb_slow")->clock_edge, Edge::kNegedge);
}

}
