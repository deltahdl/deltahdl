#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §16.7's concatenation rule states that ##N specifies a delay of N clock
// ticks; the SVA engine helper that checks the cycle-by-cycle Boolean
// sequence underlies the named-sequence machinery exercised here.

TEST(CycleDelayConcat, ParenthesizedRepetitionSequenceRegisters) {
  // §16.7 sequence_abbrev on a parenthesized sequence_expr survives
  // through to lowering; the lowerer still registers the named sequence.
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

// The source the cases below share: clk rises at 5, 15, 25, ...; req is high
// for the tick at 15 alone; gnt is high for the ticks `gnt_from` to `gnt_to`
// name, both times between ticks; and a process counts the ticks at which the
// named sequence reaches its end point, keeping the last such time. §16.7
// gives each delay form what it counts.
std::string SequenceSource(const std::string& body, const std::string& gnt_from,
                           const std::string& gnt_to) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic req = 0;\n"
         "  logic gnt = 0;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
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

// §16.7: `req ##2 gnt` has gnt true at the second subsequent tick after req,
// as Figure 16-2 draws it. req is high at the tick at 15 and gnt at the tick
// at 35 alone, two ticks later, so the sequence ends once, at 35; `req ##1
// gnt` reads gnt at 25 and never matches.
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

// §16.7: a delay of 0 has the second sequence begin at the same tick the
// first ends, so `req ##0 gnt` ends at the tick at 15 where both are high.
TEST(CycleDelayConcat, DelayOfZeroReadsTheSameTick) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceSource("req ##0 gnt", "10", "10"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 15u);
}

// §16.7: `req ##[2:4] gnt` has gnt true at some tick between the second and
// the fourth after req, and the sequence ends at each such tick: gnt is high
// at the ticks at 35, 45, 55 and 65, and the first three end it, the fourth
// being five ticks after req.
TEST(CycleDelayConcat, DelayRangeEndsAtEveryTickInTheWindow) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceSource("req ##[2:4] gnt", "30", "40"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
}

// §16.7: `$` bounds a window only by the run, so `req ##[1:$] gnt` ends at a
// tick where gnt is high however many ticks after req, the one at 65 here,
// and `##[+]` stands for the same range.
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

// §16.7: `##[*]` stands for `##[0:$]`, so `req ##[*] gnt` ends at the tick req
// and gnt are both high at, 15, where `##[+]` would read gnt from 25 on and
// find it low.
TEST(CycleDelayConcat, StarRangeIncludesTheSameTick) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceSource("req ##[*] gnt", "10", "10"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 15u);
}

}  // namespace
