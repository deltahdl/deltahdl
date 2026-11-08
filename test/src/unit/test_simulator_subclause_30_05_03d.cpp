#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

constexpr uint8_t kRiseSlot = 0;

PathDelay OneDelayPath(std::string_view src_port, uint64_t ticks) {
  PathDelay pd;
  pd.src_port = std::string(src_port);
  pd.dst_port = "y";
  pd.delay_count = 1;
  pd.delays[0] = ticks;
  ExpandTransitionDelays(pd);
  return pd;
}

std::string ConditionRaceSource(std::string_view sel_value) {
  std::string src = R"(module dut(input a, b, output y);
  logic sa, sb, armed, sel;
  assign a = sa;
  assign b = sb;
  assign y = a & b;
  specify
    if (sel) (a => y) = 6;
    if (!sel) (b => y) = 4;
  endspecify
  always @(y) begin
    if (armed) $display("y=%b t=%0d", y, $time);
  end
  initial begin
    sel = )";
  src.append(sel_value);
  src += R"(;
    armed = 1'b0;
    sa = 1'b0;
    sb = 1'b0;
    #20 sb = 1'b1;
    #20 armed = 1'b1;
    #10 sa = 1'b1;
  end
  initial #48 $display("at 48 y=%b", y);
  initial #60 $display("at 60 y=%b", y);
endmodule
)";
  return src;
}

TEST(ModulePathActivityOrder,
     AnInactiveLaterPathLeavesTheEarlierLiveOneActive) {
  PathDelay disabled = OneDelayPath("a", 6);
  PathDelay live = OneDelayPath("b", 4);
  std::vector<PathCandidate> candidates = {{&disabled, 50, false},
                                           {&live, 20, true}};
  EXPECT_EQ(SelectActivePath(candidates, kRiseSlot), &live);
}

TEST(ModulePathActivityOrder, ADisabledLastInputLeavesTheLivePathGoverning) {
  SimFixture f;
  std::string out = RunCapture(ConditionRaceSource("1'b0"), f);
  EXPECT_EQ(out, "at 48 y=0\ny=1 t=54\nat 60 y=1\n");
}

TEST(ModulePathActivityOrder, AnEnabledLastInputTakesItsOwnPathDelay) {
  SimFixture f;
  std::string out = RunCapture(ConditionRaceSource("1'b1"), f);
  EXPECT_EQ(out, "at 48 y=0\ny=1 t=56\nat 60 y=1\n");
}

TEST(ModulePathActivityOrder, APathFromABitIsTimedByThatBit) {
  SimFixture f;
  std::string out = RunCapture(R"(module dut(input [1:0] a, output y);
  logic [1:0] sa;
  logic armed;
  assign a = sa;
  assign y = a[0] | a[1];
  specify
    (a[0] => y) = 3;
    (a[1] => y) = 9;
  endspecify
  always @(y) begin
    if (armed) $display("y=%b t=%0d", y, $time);
  end
  initial begin
    armed = 1'b0;
    sa = 2'b00;
    #10 armed = 1'b1;
    #10 sa[1] = 1'b1;
    #20 sa[1] = 1'b0;
    #20 sa[0] = 1'b1;
  end
endmodule
)",
                               f);
  EXPECT_EQ(out, "y=1 t=29\ny=0 t=49\ny=1 t=63\n");
}

}  // namespace
