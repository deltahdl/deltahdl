#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

TEST(MatchedEndPoint, MatchedStoresTheMatchUntilTheDestinationClockTicks) {
  EndPoints ends = EndPointsOf(
      "    @(posedge sysclk) reset ##1 inst ##1 "
      "e1(ready, proc1, proc2).matched [->1] ##1 branch_back;\n");
  EXPECT_EQ(ends.ends, 2u);
  EXPECT_EQ(ends.last_end, 120u);
}

TEST(MatchedEndPoint, TriggeredIsNotSeenFromAnotherClock) {
  SimFixture f;
  auto* ends = RunAndFindVar(
      MatchedSource(
          "    @(posedge sysclk) reset ##1 inst ##1 "
          "e1(ready, proc1, proc2).triggered [->1] ##1 branch_back;\n"),
      f, "ends");
  ASSERT_NE(ends, nullptr);
  EXPECT_EQ(ends->value.ToUint64(), 0u);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the ending clock of 'e1' differs from the clock of "
                    "the context its triggered stands in",
                    17, "16.9.11"));
}

TEST(MatchedEndPoint, AReadConsumesTheStoredMatch) {
  EndPoints ends = EndPointsOf(
      "    @(posedge sysclk) e1_inst.matched ##1 e1_inst.matched;\n");
  EXPECT_EQ(ends.ends, 0u);
}

TEST(MatchedEndPoint, AReadConsumesTheMatchOfASequenceWithALongName) {
  SimFixture f;
  auto* reads = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0, sysclk = 0, a = 0;\n"
      "  int reads = 0, last_read = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  always #8 sysclk = ~sysclk;\n"
      "  sequence a_sequence_named_past_the_small_string_buffer;\n"
      "    @(posedge clk) a ##1 a;\n"
      "  endsequence\n"
      "  always @(posedge sysclk)\n"
      "    if (a_sequence_named_past_the_small_string_buffer.matched) begin\n"
      "      reads++;\n"
      "      last_read = $time;\n"
      "    end\n"
      "  initial begin\n"
      "    #12 a = 1;\n"
      "    #20 a = 0;\n"
      "    #40 a = 1;\n"
      "    #20 a = 0;\n"
      "    #30 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "reads");
  ASSERT_NE(reads, nullptr);
  EXPECT_EQ(reads->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last_read")->value.ToUint64(), 88u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "matched may be used only in a sequence expression",
                            10, "16.13.6"));
}

}  // namespace
