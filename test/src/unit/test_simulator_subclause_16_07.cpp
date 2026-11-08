#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(CycleDelayConcat, ParenthesizedRepetitionSequenceRegisters) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  sequence rep;\n"
      "    @(posedge clk) (a ##1 b)[*2];\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_NE(f.ctx.FindSequenceDecl("rep"), nullptr);
}

TEST(CycleDelayConcat, NamedSequenceWithConcatRegisters) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b, c;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##2 c;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_NE(f.ctx.FindSequenceDecl("abc"), nullptr);
  auto* ep = f.ctx.FindVariable("__seq_abc");
  ASSERT_NE(ep, nullptr);
  EXPECT_TRUE(ep->is_event);
}

std::string SequenceSource(const std::string& body, const std::string& gnt_from,
                           const std::string& gnt_to) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic req = 0;\n"
         "  logic gnt = 0;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  localparam int P = 4;\n"
         "  always #5 clk = ~clk;\n"
         "  sequence s;\n"
         "    @(posedge clk) " +
         body +
         ";\n"
         "  endsequence\n"
         "  initial begin\n"
         "    #10 req = 1;\n"
         "    #10 req = 0;\n"
         "  end\n"
         "  initial begin\n"
         "    #" +
         gnt_from + " gnt = 1;\n    #" + gnt_to +
         " gnt = 0;\n"
         "    #30 $finish;\n"
         "  end\n"
         "  initial forever begin\n"
         "    wait (s.triggered);\n"
         "    hits = hits + 1;\n"
         "    last = $time;\n"
         "    @(posedge clk);\n"
         "  end\n"
         "endmodule\n";
}

TEST(CycleDelayConcat, DelayOfTwoReadsTheSecondSubsequentTick) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceSource("req ##2 gnt", "30", "10"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
  SimFixture g;
  auto* none =
      RunAndFindVar(SequenceSource("req ##1 gnt", "30", "10"), g, "hits");
  ASSERT_NE(none, nullptr);
  EXPECT_EQ(none->value.ToUint64(), 0u);
}

TEST(CycleDelayConcat, DelayOfZeroReadsTheSameTick) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceSource("req ##0 gnt", "10", "10"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 15u);
}

TEST(CycleDelayConcat, DelayRangeEndsAtEveryTickInTheWindow) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceSource("req ##[2:4] gnt", "30", "40"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
}

TEST(CycleDelayConcat, UnboundedRangeReachesADistantTick) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceSource("req ##[1:$] gnt", "60", "10"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 65u);
  SimFixture g;
  auto* plus =
      RunAndFindVar(SequenceSource("req ##[+] gnt", "60", "10"), g, "hits");
  ASSERT_NE(plus, nullptr);
  EXPECT_EQ(plus->value.ToUint64(), 1u);
}

TEST(CycleDelayConcat, StarRangeIncludesTheSameTick) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceSource("req ##[*] gnt", "10", "10"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 15u);
}

TEST(CycleDelayConcat, AParameterBoundIsItsValue) {
  for (const char* body :
       {"req ##P gnt", "req ##(P) gnt", "req ##[P:P+1] gnt"}) {
    SimFixture f;
    auto* hits = RunAndFindVar(SequenceSource(body, "50", "10"), f, "hits");
    ASSERT_NE(hits, nullptr) << body;
    EXPECT_EQ(hits->value.ToUint64(), 1u) << body;
    EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u) << body;
  }
}

}  // namespace
