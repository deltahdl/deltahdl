#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_sequence_ticks.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The source the cases share: clk rises at 5, 15, 25, ...; the eight-bit v
// holds 8'h02 for the tick at 15 and 8'h01 for the tick at 25, both written
// between ticks; and a process counts the ticks at which the named sequence
// `rule`, declared as `decls` has it, reaches its end point, keeping the last
// such time.
std::string TypedSource(const std::string& decls) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic [7:0] v = 0;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  always #5 clk = ~clk;\n" +
         decls +
         "  initial begin\n"
         "    #10 v = 8'h02;\n"
         "    #10 v = 8'h01;\n"
         "    #10 v = 0;\n"
         "    #30 $finish;\n"
         "  end\n"
         "  initial forever begin\n"
         "    wait (rule.triggered);\n"
         "    hits = hits + 1;\n"
         "    last = $time;\n"
         "    @(posedge clk);\n"
         "  end\n"
         "endmodule\n";
}

// §16.8.1 (c): an actual passed to a formal of type bit is cast to bit by
// truncation, so s2's x reads bit'(v): 8'h02 truncates to 0 and 8'h01 to 1,
// and the one-operand sequence ends at the tick at 25 alone, where an untyped
// formal would read 8'h02 as true at 15 as well.
TEST(TypedSequenceFormals, ActualIsCastToTheFormalsType) {
  SimFixture f;
  auto* hits = RunAndFindVar(TypedSource("  sequence s2(bit x);\n"
                                         "    x;\n"
                                         "  endsequence\n"
                                         "  sequence rule;\n"
                                         "    @(posedge clk) s2(v);\n"
                                         "  endsequence\n"),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
  SimFixture g;
  auto* untyped = RunAndFindVar(TypedSource("  sequence s1(x);\n"
                                            "    x;\n"
                                            "  endsequence\n"
                                            "  sequence rule;\n"
                                            "    @(posedge clk) s1(v);\n"
                                            "  endsequence\n"),
                                g, "hits");
  ASSERT_NE(untyped, nullptr);
  EXPECT_EQ(untyped->value.ToUint64(), 2u);
}

// §16.8.1 (b): a formal of type event takes an event_expression, so
// event_arg_example(posedge clk) is `@(posedge clk) x ##1 y`: v reads 2 at 15
// and 1 at 25, and the sequence ends at 25.
TEST(TypedSequenceFormals, EventFormalTakesTheClockingEvent) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(TypedSource("  sequence event_arg_example(event ev);\n"
                                "    @(ev) v == 2 ##1 v == 1;\n"
                                "  endsequence\n"
                                "  sequence rule;\n"
                                "    event_arg_example(posedge clk);\n"
                                "  endsequence\n"),
                    f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

// §16.8.1: an actual meant to be combined with an edge is passed to a formal
// not typed event, so event_arg_example2(clk) with `@(posedge sig)` over the
// formal sig is `@(posedge clk) x ##1 y` as well.
TEST(TypedSequenceFormals, SignalFormalUnderAnEdgeTakesTheSignal) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(TypedSource("  sequence event_arg_example2(reg sig);\n"
                                "    @(posedge sig) v == 2 ##1 v == 1;\n"
                                "  endsequence\n"
                                "  sequence rule;\n"
                                "    event_arg_example2(clk);\n"
                                "  endsequence\n"),
                    f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

// §16.8.1: a typed formal referenced in a cycle_delay_range is a shortint,
// int or longint whose actual is an elaboration-time constant, a parameter
// here: delay_arg_example(my_delay, my_delay - 1) reads `v == 2 ##2 v == 0
// ##1 v == 0`, which with v at 2 for the tick at 15 and 0 from the tick at 35
// ends at 45.
TEST(TypedSequenceFormals, TypedDelayFormalTakesAConstantActual) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      TypedSource(
          "  parameter my_delay = 2;\n"
          "  sequence delay_arg_example(shortint delay1, delay2);\n"
          "    v == 2 ##delay1 v == 0 ##delay2 v == 0;\n"
          "  endsequence\n"
          "  sequence rule;\n"
          "    @(posedge clk) delay_arg_example(my_delay, my_delay - 1);\n"
          "  endsequence\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

// §16.8.1 (a): a formal of type sequence stands for the sequence bound to it,
// a sequence expression or a named sequence. With a, b and c holding the
// bits of av, bv and cv at the rises of clk, a ##1 b ##1 c matches from the
// rises at 5 and 55, twice, and a ##1 b from 5, 25 and 55, three times.
std::string SequenceFormalSource() {
  return "module t;\n"
         "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
         "  bit [0:9] av = 10'b1010010000, bv = 10'b0101001010,\n"
         "            cv = 10'b0010000100;\n"
         "  bit a, b, c;\n"
         "  assign a = av[0]; assign b = bv[0]; assign c = cv[0];\n"
         "  always @(negedge clk) begin\n"
         "    av <= av << 1; bv <= bv << 1; cv <= cv << 1;\n"
         "  end\n"
         "  int cseq = 0, cseq2 = 0;\n"
         "  sequence s_seq(sequence sq, untyped z); sq ##1 z; endsequence\n"
         "  sequence s_seq2(sequence sq); sq; endsequence\n"
         "  sequence ab; a ##1 b; endsequence\n"
         "  cover property (@(posedge clk) s_seq(a ##1 b, c)) cseq++;\n"
         "  cover property (@(posedge clk) s_seq2(ab)) cseq2++;\n"
         "endmodule\n";
}

TEST(TypedSequenceFormals, ASequenceFormalStandsForTheSequenceBoundToIt) {
  SimFixture f;
  auto* cseq = RunAndFindVar(SequenceFormalSource(), f, "cseq");
  ASSERT_NE(cseq, nullptr);
  EXPECT_EQ(cseq->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("cseq2")->value.ToUint64(), 3u);
}

// §16.8.1 (a): a sequence formal stands for its actual wherever the body
// references it, so an actual built with `or` or `and`, referenced as one
// operand of the chain `te1 ##1 q ##1 te5`, is one sequence there. From tick
// 2, te4 ends at 3 and te2 ##1 te3 at 4, so with `or` te5 is read at 4 and 5
// and the sequence ends at both, the ticks at 35 and 45, and with `and` the
// whole ends at 4 and te5 is read at 5 alone.
TEST(TypedSequenceFormals, AnActualBuiltWithOrOrAndIsOneSequence) {
  const std::string kFramed =
      "  sequence framed(sequence q);\n"
      "    te1 ##1 q ##1 te5;\n"
      "  endsequence\n";
  SimFixture f;
  auto* either = RunAndFindVar(
      SequenceTickSource("framed(te2 ##1 te3 or te4)",
                         DriveTicks({{2}, {3}, {4}, {3}, {4, 5}}), kFramed),
      f, "hits");
  ASSERT_NE(either, nullptr);
  EXPECT_EQ(either->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 45u);
  SimFixture g;
  auto* both = RunAndFindVar(
      SequenceTickSource("framed(te2 ##1 te3 and te4)",
                         DriveTicks({{2}, {3}, {4}, {3}, {4, 5}}), kFramed),
      g, "hits");
  ASSERT_NE(both, nullptr);
  EXPECT_EQ(both->value.ToUint64(), 1u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

}  // namespace
