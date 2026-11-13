#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SequenceCompositionSim, TriggeredReflectsEndpointIndependentOfStartPoint) {
  uint64_t result = RunAndGet(
      "module t;\n"
      "  logic clk, a, b, c;\n"
      "  logic [7:0] result;\n"
      "  sequence long_seq;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  sequence short_seq;\n"
      "    @(posedge clk) c;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    clk = 0; a = 0; b = 0; c = 0; result = 0;\n"
      "    #1 a = 1; #1 clk = 1; #1 clk = 0;\n"
      "    #1 a = 0; b = 1; #1 clk = 1; #1 clk = 0;\n"
      "    #1 b = 0; c = 1; #1 clk = 1; #1 clk = 0;\n"
      "    #10 $finish;\n"
      "  end\n"
      "  initial begin\n"
      "    wait(long_seq.triggered);\n"
      "    result = (long_seq.triggered && short_seq.triggered) ? 8'd42\n"
      "                                                         : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(SequenceCompositionSim, TriggeredIsFalseWhenEndpointNotReached) {
  uint64_t result = RunAndGet(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  logic [7:0] result;\n"
      "  sequence ab;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    clk = 0; a = 1; b = 0; result = 8'hee;\n"
      "    #1 clk = 1; #1 clk = 0;\n"
      "    #1 clk = 1; #1 clk = 0;\n"
      "    result = ab.triggered ? 8'd1 : 8'd0;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 0u);
}

std::string CompositionSource(const std::string& decls,
                              const std::string& watched) {
  return "module t;\n"
         "  logic sysclk = 0;\n"
         "  int tick = 1;\n"
         "  logic trans, start_trans, a, b, c, end_trans;\n"
         "  logic reset, inst, ready, proc1, proc2, branch_back, req;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  always #5 sysclk = ~sysclk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign trans = tick inside {1};\n"
         "  assign start_trans = tick inside {2};\n"
         "  assign a = tick inside {3};\n"
         "  assign b = tick inside {4};\n"
         "  assign c = tick inside {5};\n"
         "  assign end_trans = tick inside {6};\n"
         "  assign reset = tick inside {11, 21};\n"
         "  assign inst = tick inside {12, 22};\n"
         "  assign ready = tick inside {11, 12, 13, 23, 24, 25};\n"
         "  assign proc1 = tick inside {12, 24};\n"
         "  assign proc2 = tick inside {13, 25};\n"
         "  assign branch_back = tick inside {14, 26};\n"
         "  assign req = tick inside {31, 32};\n" +
         decls +
         "  initial forever begin\n"
         "    wait (" +
         watched +
         ".triggered);\n"
         "    hits = hits + 1;\n"
         "    last = tick;\n"
         "    @(posedge sysclk);\n"
         "  end\n"
         "  initial #350 $finish;\n"
         "endmodule\n";
}

const char* const kE1 =
    "  sequence e1;\n"
    "    @(posedge sysclk) $rose(ready) ##1 proc1 ##1 proc2;\n"
    "  endsequence\n";

TEST(SequenceComposition, InstanceMatchesFromTheTickItIsReached) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      CompositionSource("  sequence s;\n"
                        "    a ##1 b ##1 c;\n"
                        "  endsequence\n"
                        "  sequence rule;\n"
                        "    @(posedge sysclk) trans ##1 start_trans ##1 s ##1 "
                        "end_trans;\n"
                        "  endsequence\n",
                        "rule"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 6u);
}

TEST(SequenceComposition, TriggeredDetectsTheEndPointWhateverTheStart) {
  SimFixture f;
  auto* by_endpoint = RunAndFindVar(
      CompositionSource(std::string(kE1) +
                            "  sequence rule;\n"
                            "    @(posedge sysclk) reset ##1 inst ##1 "
                            "e1.triggered ##1 branch_back;\n"
                            "  endsequence\n",
                        "rule"),
      f, "hits");
  ASSERT_NE(by_endpoint, nullptr);
  EXPECT_EQ(by_endpoint->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 14u);
  SimFixture g;
  auto* by_instance = RunAndFindVar(
      CompositionSource(std::string(kE1) +
                            "  sequence rule;\n"
                            "    @(posedge sysclk) reset ##1 inst ##1 e1 ##1 "
                            "branch_back;\n"
                            "  endsequence\n",
                        "rule"),
      g, "hits");
  ASSERT_NE(by_instance, nullptr);
  EXPECT_EQ(by_instance->value.ToUint64(), 1u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 26u);
}

TEST(SequenceComposition, TriggeredAppliesToAnInstanceWithArguments) {
  const std::string kE2 =
      "  sequence e2(a, b, c);\n"
      "    @(posedge sysclk) $rose(a) ##1 b ##1 c;\n"
      "  endsequence\n";
  SimFixture f;
  auto* direct = RunAndFindVar(
      CompositionSource(kE2 + "  sequence rule2;\n"
                              "    @(posedge sysclk) reset ##1 inst ##1 "
                              "e2(ready, proc1, proc2).triggered ##1 "
                              "branch_back;\n"
                              "  endsequence\n",
                        "rule2"),
      f, "hits");
  ASSERT_NE(direct, nullptr);
  EXPECT_EQ(direct->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 14u);
  SimFixture g;
  auto* named = RunAndFindVar(
      CompositionSource(kE2 + "  sequence e2_instantiated;\n"
                              "    e2(ready, proc1, proc2);\n"
                              "  endsequence\n"
                              "  sequence rule2a;\n"
                              "    @(posedge sysclk) reset ##1 inst ##1 "
                              "e2_instantiated.triggered ##1 branch_back;\n"
                              "  endsequence\n",
                        "rule2a"),
      g, "hits");
  ASSERT_NE(named, nullptr);
  EXPECT_EQ(named->value.ToUint64(), 1u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 14u);
}

TEST(SequenceComposition, EmptyMatchDoesNotActivateTriggeredLive) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      CompositionSource("  sequence zero_or_one_req;\n"
                        "    @(posedge sysclk) (req==1'b1)[*0:1];\n"
                        "  endsequence\n",
                        "zero_or_one_req"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 32u);
}

TEST(SequenceComposition, TriggeredAppliesToASequenceFormalsInstanceActual) {
  SimFixture f;
  auto* c = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] xv = 10'b0110000000, yv = 10'b0010000000,\n"
      "            zv = 10'b0001000000, wv = 10'b0000100000;\n"
      "  bit x, y, z, w;\n"
      "  assign x = xv[0]; assign y = yv[0]; assign z = zv[0];\n"
      "  assign w = wv[0];\n"
      "  always @(negedge clk) begin\n"
      "    xv <= xv << 1; yv <= yv << 1; zv <= zv << 1; wv <= wv << 1;\n"
      "  end\n"
      "  int c = 0, c2 = 0;\n"
      "  sequence e2(a, b, cc); @(posedge clk) $rose(a) ##1 b ##1 cc;\n"
      "  endsequence\n"
      "  sequence e3(sequence a, untyped b);\n"
      "    @(posedge clk) a.triggered ##1 b;\n"
      "  endsequence\n"
      "  cover property (e3(e2(x, y, z), w)) c++;\n"
      "  cover property (@(posedge clk) e2(x, y, z).triggered) c2++;\n"
      "endmodule\n",
      f, "c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("c2")->value.ToUint64(), 1u);
}

TEST(SequenceComposition, AClocklessSequenceTakesTheClockOfItsContext) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  int c1 = 0, c2 = 0;\n"
      "  sequence r; e.triggered ##1 1; endsequence\n"
      "  sequence e; 1 ##1 1; endsequence\n"
      "  cover property (@(posedge clk) r) c1++;\n"
      "  cover property (@(posedge clk) e.triggered) c2++;\n"
      "  initial #97 $display(\"c1=%0d c2=%0d\", c1, c2);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=8 c2=9\n"), std::string::npos);
}

TEST(SequenceComposition, AClocklessInstanceTakesTheClockOfItsContext) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  int c1 = 0;\n"
      "  sequence sub_plain(x); x ##1 1; endsequence\n"
      "  sequence r; sub_plain(1).triggered ##1 1; endsequence\n"
      "  cover property (@(posedge clk) r) c1++;\n"
      "  initial #97 $display(\"c1=%0d\", c1);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=8\n"), std::string::npos);
}

TEST(SequenceComposition, EachContextClockGivesAClocklessSequenceItsEnds) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  int c1 = 0, c2 = 0, c3 = 0;\n"
      "  sequence e; 1 ##1 1; endsequence\n"
      "  cover property (@(posedge clk) e.triggered) c1++;\n"
      "  cover property (@(negedge clk) e.triggered) c2++;\n"
      "  cover property (@(negedge clk) e.triggered) c3++;\n"
      "  initial #97 $display(\"c1=%0d c2=%0d c3=%0d\", c1, c2, c3);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=9 c2=8 c3=8\n"), std::string::npos);
}

}  // namespace
