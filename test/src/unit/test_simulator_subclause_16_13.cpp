#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string MulticlockSource(const std::string& items) {
  return "module t;\n"
         "  logic clk0 = 0;\n"
         "  logic clk1 = 0;\n"
         "  int tick = 1;\n"
         "  logic sig0, sig1;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  int last_pass = 0;\n"
         "  always #5 clk0 = ~clk0;\n"
         "  always #10 tick = tick + 1;\n"
         "  initial begin\n"
         "    #12 clk1 = 1;\n"
         "    #8 clk1 = 0;\n"
         "    #7 clk1 = 1;\n"
         "    #8 clk1 = 0;\n"
         "    #10 clk1 = 1;\n"
         "    #5 clk1 = 0;\n"
         "    #7 clk1 = 1;\n"
         "    #8 clk1 = 0;\n"
         "    #7 clk1 = 1;\n"
         "    #6 clk1 = 0;\n"
         "  end\n"
         "  assign sig0 = tick inside {1, 2, 5, 7};\n"
         "  assign sig1 = tick inside {3, 5};\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

struct MulticlockCounts {
  uint64_t passes;
  uint64_t fails;
  uint64_t last_pass;
};

MulticlockCounts CountsOfMulticlock(const std::string& spec,
                                    const std::string& prelude = "") {
  SimFixture f;
  auto* passes = RunAndFindVar(
      MulticlockSource(prelude + "  p: assert property (@(posedge clk0) " +
                       spec +
                       ") begin passes++; last_pass = $time; end "
                       "else fails++;\n"),
      f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  Variable* last_pass = f.ctx.FindVariable("last_pass");
  return {passes->value.ToUint64(), fails->value.ToUint64(),
          last_pass->value.ToUint64()};
}

void ExpectAsWithoutTheRedundantClock(const std::string& spec,
                                      const std::string& plain,
                                      const std::string& prelude = "") {
  MulticlockCounts named = CountsOfMulticlock(spec, prelude);
  MulticlockCounts bare = CountsOfMulticlock(plain);
  EXPECT_NE(bare.passes + bare.fails, 0u) << plain;
  EXPECT_EQ(named.passes, bare.passes) << spec;
  EXPECT_EQ(named.fails, bare.fails) << spec;
  EXPECT_EQ(named.last_pass, bare.last_pass) << spec;
}

TEST(MulticlockSequences, ASingleDelayMovesToTheNextTickOfTheSecondClock) {
  MulticlockCounts counts = CountsOfMulticlock("sig0 ##1 @(posedge clk1) sig1");
  EXPECT_EQ(counts.passes, 1u);
  EXPECT_EQ(counts.fails, 7u);
  EXPECT_EQ(counts.last_pass, 27u);
}

TEST(MulticlockSequences, AZeroDelayMovesToTheOverlappingTickWhereThereIsOne) {
  MulticlockCounts counts = CountsOfMulticlock("sig0 ##0 @(posedge clk1) sig1");
  EXPECT_EQ(counts.passes, 2u);
  EXPECT_EQ(counts.fails, 6u);
  EXPECT_EQ(counts.last_pass, 45u);
}

TEST(MulticlockSequences, TheSameClockNamedAgainChangesNothing) {
  MulticlockCounts counts = CountsOfMulticlock("sig0 ##1 @(posedge clk0) sig1");
  EXPECT_EQ(counts.passes, 1u);
  EXPECT_EQ(counts.fails, 7u);
  EXPECT_EQ(counts.last_pass, 25u);
  MulticlockCounts plain = CountsOfMulticlock("sig0 ##1 sig1");
  EXPECT_EQ(plain.passes, 1u);
  EXPECT_EQ(plain.fails, 7u);
  EXPECT_EQ(plain.last_pass, 25u);
}

TEST(MulticlockSequences, ABareNamedClockIsTheParenthesisedOnesEvent) {
  MulticlockCounts paren = CountsOfMulticlock("sig0 ##1 @(clk1) sig1");
  EXPECT_EQ(paren.passes, 1u);
  EXPECT_EQ(paren.fails, 7u);
  EXPECT_EQ(paren.last_pass, 50u);
  MulticlockCounts bare = CountsOfMulticlock("sig0 ##1 @clk1 sig1");
  EXPECT_EQ(bare.passes, 1u);
  EXPECT_EQ(bare.fails, 7u);
  EXPECT_EQ(bare.last_pass, 50u);
}

std::string EventClockSource(const std::string& second_clock,
                             const std::string& leading_clock) {
  return "module t;\n"
         "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
         "  logic nclk; assign nclk = ~clk;\n"
         "  bit [0:9] av = 10'b1010010000, bv = 10'b0110011010;\n"
         "  bit a, b; assign a = av[0]; assign b = bv[0];\n"
         "  always @(negedge clk) av <= av << 1;\n"
         "  always @(posedge clk) bv <= bv << 1;\n"
         "  event ne; always @(negedge clk) -> ne;\n"
         "  int second = 0, leading = 0;\n"
         "  cover property (@(posedge clk) a ##1 @(" +
         second_clock +
         ") b) second++;\n"
         "  cover property (@(" +
         leading_clock +
         ") b ##1 @(posedge clk) a) leading++;\n"
         "endmodule\n";
}

TEST(MulticlockSequences, ANamedEventClocksASubsequenceAsASignalEdgeDoes) {
  SimFixture f;
  auto* second = RunAndFindVar(EventClockSource("ne", "ne"), f, "second");
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(second->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("leading")->value.ToUint64(), 2u);
  SimFixture g;
  auto* edge = RunAndFindVar(EventClockSource("posedge nclk", "posedge nclk"),
                             g, "second");
  ASSERT_NE(edge, nullptr);
  EXPECT_EQ(edge->value.ToUint64(), 2u);
  EXPECT_EQ(g.ctx.FindVariable("leading")->value.ToUint64(), 2u);
}

TEST(MulticlockSequences, AnotherClockTickingFirstBeginsNoAttempt) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  logic nclk; assign nclk = ~clk;\n"
      "  bit a = 1, b = 1;\n"
      "  int hits = 0;\n"
      "  cover property (@(posedge clk) a ##1 @(posedge nclk) b) hits++;\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 10u);
}

TEST(MulticlockSequences, AClockNamedByAPathTicksAsItsSignalDoes) {
  SimFixture f;
  auto* path = RunAndFindVar(
      "interface ifc(input logic clk);\n"
      "endinterface\n"
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b1101001111;\n"
      "  bit [0:19] bv = 20'b01101001011101000110;\n"
      "  always @(posedge clk) av <= av << 1;\n"
      "  always @(clk) bv <= bv << 1;\n"
      "  bit a, b; assign a = av[0]; assign b = bv[0];\n"
      "  ifc i0(clk);\n"
      "  int c1 = 0, c2 = 0;\n"
      "  cover property (@(posedge clk) a ##1 @(negedge i0.clk) b) c1++;\n"
      "  cover property (@(posedge clk) a ##1 @(negedge clk) b) c2++;\n"
      "endmodule\n",
      f, "c1");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("c2")->value.ToUint64(), 4u);
}

TEST(MulticlockSequences, AnInstancesSecondClockTickingFirstBeginsNoAttempt) {
  SimFixture f;
  auto* fi = RunAndFindVar(
      "interface ifc(input logic clk);\n"
      "  logic a, b;\n"
      "  property p_clk; @(posedge clk) a ##1 @(negedge clk) b; endproperty\n"
      "endinterface\n"
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b1101001111, bv = 10'b0110011110;\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  logic a, b; assign a = av[0]; assign b = bv[0];\n"
      "  ifc i0(clk);\n"
      "  assign i0.a = a; assign i0.b = b;\n"
      "  property m_clk; @(posedge clk) a ##1 @(negedge clk) b; endproperty\n"
      "  int fi = 0, fm = 0;\n"
      "  assert property (i0.p_clk) else fi++;\n"
      "  assert property (m_clk) else fm++;\n"
      "endmodule\n",
      f, "fi");
  ASSERT_NE(fi, nullptr);
  EXPECT_EQ(fi->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("fm")->value.ToUint64(), 6u);
}

TEST(MulticlockSequences,
     AnInstanceWithActualsBeginsNoAttemptAtItsSecondClock) {
  SimFixture f;
  auto* fi = RunAndFindVar(
      "module t;\n"
      "  logic clk; initial begin clk = 0; repeat (20) #5 clk = ~clk; end\n"
      "  bit [0:9] av = 10'b1101001111, bv = 10'b0110011110;\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  logic a, b; assign a = av[0]; assign b = bv[0];\n"
      "  property pm(x, y); @(posedge clk) x ##1 @(negedge clk) y; "
      "endproperty\n"
      "  int fi = 0, fm = 0;\n"
      "  assert property (pm(a, b)) else fi++;\n"
      "  assert property (@(posedge clk) a ##1 @(negedge clk) b) else fm++;\n"
      "endmodule\n",
      f, "fi");
  ASSERT_NE(fi, nullptr);
  EXPECT_EQ(fi->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("fm")->value.ToUint64(), 6u);
}

TEST(MulticlockSequences, ClocksNamedByPathsThroughTwoInstancesAreTwoClocks) {
  SimFixture f;
  auto* path = RunAndFindVar(
      "interface ifc(input logic clk);\n"
      "endinterface\n"
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  logic nclk; assign nclk = ~clk;\n"
      "  bit a = 1, b = 1;\n"
      "  initial begin #7; repeat (18) #5 b = ~b; end\n"
      "  ifc i0(clk), i1(nclk);\n"
      "  int c1 = 0, c2 = 0;\n"
      "  cover property (@(posedge i0.clk) a ##1 @(posedge i1.clk) b) c1++;\n"
      "  cover property (@(posedge clk) a ##1 @(posedge nclk) b) c2++;\n"
      "endmodule\n",
      f, "c1");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("c2")->value.ToUint64(), 10u);
}

TEST(MulticlockSequences, ARepeatedGroupNamingTheClockInForceIsUnclocked) {
  MulticlockCounts counts =
      CountsOfMulticlock("(@(posedge clk0) sig0 ##1 1)[*2]");
  EXPECT_EQ(counts.passes, 1u);
  EXPECT_EQ(counts.fails, 6u);
  EXPECT_EQ(counts.last_pass, 75u);
  ExpectAsWithoutTheRedundantClock("(@(posedge clk0) sig0 ##1 1)[*2]",
                                   "(sig0 ##1 1)[*2]");
}

TEST(MulticlockSequences, AClockNamedAgainInAnyOperandChangesNothing) {
  ExpectAsWithoutTheRedundantClock("(@(posedge clk0) sig0 ##1 1)[*1:2]",
                                   "(sig0 ##1 1)[*1:2]");
  ExpectAsWithoutTheRedundantClock("(@(posedge clk0) sig0)[*2]", "sig0[*2]");
  ExpectAsWithoutTheRedundantClock(
      "sig0 ##1 @(posedge clk1) (@(posedge clk1) sig1 ##1 1)[*2]",
      "sig0 ##1 @(posedge clk1) sig1 ##1 1 ##1 sig1 ##1 1");
  ExpectAsWithoutTheRedundantClock(
      "(@(posedge clk0) sig1) within (sig0 ##1 1 ##1 1)",
      "sig1 within (sig0 ##1 1 ##1 1)");
  ExpectAsWithoutTheRedundantClock(
      "(@(posedge clk0) sig0 ##1 1) intersect (1 ##1 sig1)",
      "(sig0 ##1 1) intersect (1 ##1 sig1)");
  ExpectAsWithoutTheRedundantClock("sig0 ##2 @(posedge clk0) sig1",
                                   "sig0 ##2 sig1");
  ExpectAsWithoutTheRedundantClock("sig0 throughout (@(posedge clk0) 1 ##1 1)",
                                   "sig0 throughout (1 ##1 1)");
}

TEST(MulticlockSequences, AGroupRepeatedAfterAClockChangeIsReadOnThatClock) {
  ExpectAsWithoutTheRedundantClock(
      "sig0 ##1 @(posedge clk1) (sig1 ##1 1)[*2]",
      "sig0 ##1 @(posedge clk1) sig1 ##1 1 ##1 sig1 ##1 1");
}

TEST(MulticlockSequences, ARedundantClockInADeclarationChangesNothing) {
  ExpectAsWithoutTheRedundantClock(
      "sc0[*2]", "(sig0 ##1 1)[*2]",
      "  sequence sc0; @(posedge clk0) sig0 ##1 1; endsequence\n");
  ExpectAsWithoutTheRedundantClock(
      "r", "(sig0 ##1 1)[*2]",
      "  sequence r; @(posedge clk0) (@(posedge clk0) sig0 ##1 1)[*2]; "
      "endsequence\n");
  ExpectAsWithoutTheRedundantClock(
      "q", "(sig0 ##1 1)[*2]",
      "  property q; @(posedge clk0) (@(posedge clk0) sig0 ##1 1)[*2]; "
      "endproperty\n");
}

}  // namespace
