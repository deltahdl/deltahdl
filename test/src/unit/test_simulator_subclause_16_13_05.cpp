#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The design of test/src/e2e/matched_end_point.sv around one destination
// sequence: e1 on clk, rising at 5, 15, ..., matches at 35 and 95, and the
// destination is on sysclk, rising at 8, 24, 40, ..., never together with
// clk; the process counts the end points the destination reaches and keeps
// the time of the last.
std::string MatchedSource(const std::string& destination) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic sysclk = 0;\n"
         "  logic ready = 0, proc1 = 0, proc2 = 0;\n"
         "  logic reset = 0, inst = 0, branch_back = 0;\n"
         "  int ends = 0;\n"
         "  int last_end = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #8 sysclk = ~sysclk;\n"
         "  sequence e1(a, b, c);\n"
         "    @(posedge clk) $rose(a) ##1 b ##1 c;\n"
         "  endsequence\n"
         "  sequence e1_inst;\n"
         "    e1(ready, proc1, proc2);\n"
         "  endsequence\n"
         "  sequence dest;\n" +
         destination +
         "  endsequence\n"
         "  initial forever begin\n"
         "    wait (dest.triggered);\n"
         "    ends++;\n"
         "    last_end = $time;\n"
         "    @(posedge sysclk);\n"
         "  end\n"
         "  initial begin\n"
         "    #5 reset = 1;\n"
         "    #5 reset = 0; ready = 1;\n"
         "    #10 inst = 1; proc1 = 1;\n"
         "    #10 inst = 0; proc1 = 0; proc2 = 1;\n"
         "    #10 proc2 = 0;\n"
         "    #10 ready = 0; branch_back = 1;\n"
         "    #10 branch_back = 0;\n"
         "    #10 reset = 1; ready = 1;\n"
         "    #5 reset = 0;\n"
         "    #5 inst = 1; proc1 = 1;\n"
         "    #10 inst = 0; proc1 = 0; proc2 = 1;\n"
         "    #10 proc2 = 0;\n"
         "    #15 branch_back = 1;\n"
         "    #10 branch_back = 0;\n"
         "    #5 $finish;\n"
         "  end\n"
         "endmodule\n";
}

// The end points the destination sequence reached, and the time of the
// last.
struct EndPoints {
  uint64_t ends;
  uint64_t last_end;
};

EndPoints EndPointsOf(const std::string& destination) {
  SimFixture f;
  auto* ends = RunAndFindVar(MatchedSource(destination), f, "ends");
  if (ends == nullptr) return {~0ull, ~0ull};
  Variable* last_end = f.ctx.FindVariable("last_end");
  return {ends->value.ToUint64(), last_end->value.ToUint64()};
}

// §16.13.5: matched stores the result of the source match, at 35 and 95 on
// clk, until the first tick of sysclk after it, 40 and 104, where the
// clause's e2 reads it and goes on to branch_back, ending at 56 and 120.
TEST(MatchedEndPoint, MatchedStoresTheMatchUntilTheDestinationClockTicks) {
  EndPoints ends = EndPointsOf(
      "    @(posedge sysclk) reset ##1 inst ##1 "
      "e1(ready, proc1, proc2).matched [->1] ##1 branch_back;\n");
  EXPECT_EQ(ends.ends, 2u);
  EXPECT_EQ(ends.last_end, 120u);
}

// §16.13.5: triggered is true at the time step of the match alone, which
// is no tick of sysclk, so the same sequence over triggered never ends.
TEST(MatchedEndPoint, TriggeredIsNotSeenFromAnotherClock) {
  EndPoints ends = EndPointsOf(
      "    @(posedge sysclk) reset ##1 inst ##1 "
      "e1(ready, proc1, proc2).triggered [->1] ##1 branch_back;\n");
  EXPECT_EQ(ends.ends, 0u);
}

// §16.13.5: the stored match is consumed by the first read after it, so a
// second read at the next tick of sysclk is false, and a sequence reading
// matched at consecutive ticks never ends.
TEST(MatchedEndPoint, AReadConsumesTheStoredMatch) {
  EndPoints ends = EndPointsOf(
      "    @(posedge sysclk) e1_inst.matched ##1 e1_inst.matched;\n");
  EXPECT_EQ(ends.ends, 0u);
}

}  // namespace
