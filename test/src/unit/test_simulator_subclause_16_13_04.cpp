#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string ExamplesSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic clk1 = 0;\n"
         "  logic clk2 = 0;\n"
         "  int tick = 1;\n"
         "  logic a, b, c, d, e, f;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  int fail_sum = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  initial begin\n"
         "    #12 clk1 = 1; #8 clk1 = 0; #7 clk1 = 1; #8 clk1 = 0;\n"
         "    #10 clk1 = 1; #5 clk1 = 0; #7 clk1 = 1; #8 clk1 = 0;\n"
         "    #7 clk1 = 1; #6 clk1 = 0;\n"
         "  end\n"
         "  initial begin\n"
         "    #8 clk2 = 1; #8 clk2 = 0; #9 clk2 = 1; #7 clk2 = 0;\n"
         "    #6 clk2 = 1; #8 clk2 = 0; #9 clk2 = 1; #7 clk2 = 0;\n"
         "    #8 clk2 = 1; #4 clk2 = 0; #4 clk2 = 1; #1 clk2 = 0;\n"
         "  end\n"
         "  assign a = tick inside {1, 2};\n"
         "  assign b = tick inside {3, 5};\n"
         "  assign c = tick inside {3, 4, 6};\n"
         "  assign d = tick inside {6, 7};\n"
         "  assign e = tick inside {3};\n"
         "  assign f = tick inside {4};\n"
         "  sequence s1;\n"
         "    a ##1 b;\n"
         "  endsequence\n"
         "  sequence s2;\n"
         "    c ##1 d;\n"
         "  endsequence\n"
         "  sequence mult_s;\n"
         "    @(posedge clk) a ##1 @(posedge clk1) s1 ##1 @(posedge clk2) s2;\n"
         "  endsequence\n"
         "  property mult_p1;\n"
         "    @(posedge clk) a ##1 @(posedge clk1) s1 ##1 @(posedge clk2) s2;\n"
         "  endproperty\n"
         "  property mult_p2;\n"
         "    mult_s;\n"
         "  endproperty\n"
         "  property mult_p3;\n"
         "    @(posedge clk) a ##1 @(posedge clk1) s1 |=> @(posedge clk2) s2;\n"
         "  endproperty\n"
         "  property mult_p6;\n"
         "    mult_s |=> mult_s;\n"
         "  endproperty\n"
         "  property mult_p7;\n"
         "    @(posedge clk) a ##1 b |-> c ##1 @(posedge clk1) d;\n"
         "  endproperty\n"
         "  property mult_p8;\n"
         "    @(posedge clk) a ##1 b |->\n"
         "      if (c)\n"
         "        (1 |=> @(posedge clk1) d)\n"
         "      else\n"
         "        e ##1 @(posedge clk2) f ;\n"
         "  endproperty\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

struct ExampleCounts {
  uint64_t passes;
  uint64_t fails;
  uint64_t fail_sum;
};

ExampleCounts CountsOfExample(const std::string& spec) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ExamplesSource("  p: assert property (" + spec +
                     ") passes++; else begin fails++; fail_sum += $time; "
                     "end\n"),
      f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  Variable* fail_sum = f.ctx.FindVariable("fail_sum");
  return {passes->value.ToUint64(), fails->value.ToUint64(),
          fail_sum->value.ToUint64()};
}

TEST(MulticlockExamples, TheMulticlockSequenceMatchesAcrossItsThreeClocks) {
  ExampleCounts seq = CountsOfExample("mult_s");
  EXPECT_EQ(seq.passes, 1u);
  EXPECT_EQ(seq.fails, 7u);
  EXPECT_EQ(seq.fail_sum, 327u);
  ExampleCounts prop = CountsOfExample("mult_p1");
  EXPECT_EQ(prop.passes, 1u);
  EXPECT_EQ(prop.fails, 7u);
  EXPECT_EQ(prop.fail_sum, 327u);
}

TEST(MulticlockExamples, ANamedMulticlockSequenceIsAPropertyBody) {
  ExampleCounts counts = CountsOfExample("mult_p2");
  EXPECT_EQ(counts.passes, 1u);
  EXPECT_EQ(counts.fails, 7u);
  EXPECT_EQ(counts.fail_sum, 327u);
}

TEST(MulticlockExamples, TheMulticlockImplicationReadsItsConsequentOnItsClock) {
  ExampleCounts counts = CountsOfExample("mult_p3");
  EXPECT_EQ(counts.passes, 8u);
  EXPECT_EQ(counts.fails, 0u);
}

TEST(MulticlockExamples,
     NamedMulticlockSequencesStandOnBothSidesOfAnImplication) {
  ExampleCounts counts = CountsOfExample("mult_p6");
  EXPECT_EQ(counts.passes, 7u);
  EXPECT_EQ(counts.fails, 1u);
  EXPECT_EQ(counts.fail_sum, 65u);
}

TEST(MulticlockExamples, ClockFlowPutsTheUnclockedOperandsOnTheLeadingClock) {
  ExampleCounts overlapped = CountsOfExample("mult_p7");
  EXPECT_EQ(overlapped.passes, 7u);
  EXPECT_EQ(overlapped.fails, 1u);
  EXPECT_EQ(overlapped.fail_sum, 27u);
  ExampleCounts branched = CountsOfExample("mult_p8");
  EXPECT_EQ(branched.passes, 7u);
  EXPECT_EQ(branched.fails, 1u);
  EXPECT_EQ(branched.fail_sum, 27u);
}

}  // namespace
