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

// §16.8.1 (c): each keyword data type casts its actual so: byte'(v +
// 9'h100) drops the ninth bit and reads 2 where v is 2, at 15 alone, where
// uncast it would read 9'h102; longint and integer widen, logic keeps the
// least significant bit, 0 at 15, and logic [1:0] the two least significant
// bits, 2 at 15.
TEST(TypedSequenceFormals, EachKeywordTypeCastsItsActual) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      TypedSource("  sequence s_k(byte b, longint l, integer i, logic g,\n"
                  "               logic [1:0] n);\n"
                  "    b == 2 && l == 2 && i == 2 && g == 0 && n == 2;\n"
                  "  endsequence\n"
                  "  sequence rule;\n"
                  "    @(posedge clk) s_k(v + 9'h100, v, v, v, v);\n"
                  "  endsequence\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 15u);
}

// §16.8.1 (c): a formal typed with packed dimensions, or with a type name no
// keyword spells, casts an actual that is no variable_lvalue to that type as
// a keyword type does: n, t and p read v + 8'h10, v + 8'h20 and v + 8'h30 as
// the two bits logic [1:0], two_t and pk::two_t hold, 2 where v is 2, and q
// reads v + 8'h44 as the four bits of two_t [1:0], 6 there; so the sequence
// ends at 15 alone. Uncast, they would read 8'h12, 8'h22, 8'h32 and 8'h46
// there, and q cast to the two bits two_t alone holds would read 2.
TEST(TypedSequenceFormals, APackedOrNamedTypeCastsItsActual) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "package pk;\n"
      "  typedef logic [1:0] two_t;\n"
      "endpackage\n" +
          TypedSource("  typedef logic [1:0] two_t;\n"
                      "  sequence s_p(logic [1:0] n, two_t t, pk::two_t p,\n"
                      "               two_t [1:0] q);\n"
                      "    n == 2 && t == 2 && p == 2 && q == 6;\n"
                      "  endsequence\n"
                      "  sequence rule;\n"
                      "    @(posedge clk)\n"
                      "      s_p(v + 8'h10, v + 8'h20, v + 8'h30, v + 8'h44);\n"
                      "  endsequence\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 15u);
}

// §16.8.1 (c): an actual that is a variable_lvalue -- a name, a select or
// member of one, or a concatenation of such -- is read through references to
// the formal as having the formal's type. n reads u, 8'hF1 at 25, as the
// four bits logic [3:0] holds, 1, and e reads it as four two_t elements, of
// which e[3] is 2'b11; a select of w or m resolves against the [8:1] w is
// declared with and pk::w_t names, so w[1] and m[1] are the rightmost bits of
// v[7:0] and bx.f, 1 where v is 1, as k[0] is of byte'(v); and p reads the
// concatenation as a pair_t, whose hi is 0 there, whose lo, a half_t, has b
// 1, and whose rightmost bit p[0] is 1. So the sequence ends at 25 alone.
// Read with the actuals' own types, n read 8'hF1, e[3] bit 3 of u, w[1] and
// m[1] the second bit from the right, and p.hi and p.lo.b named no member of
// the concatenation, so the sequence never ended.
TEST(TypedSequenceFormals, AVariableLvalueActualReadsWithTheFormalsType) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "package pk;\n"
      "  typedef logic [8:1] w_t;\n"
      "endpackage\n" +
          TypedSource(
              "  wire [7:0] u = v + 8'hF0;\n"
              "  typedef logic [1:0] two_t;\n"
              "  typedef struct packed { logic [7:0] f; } box_t;\n"
              "  typedef struct packed { logic [1:0] a, b; } half_t;\n"
              "  typedef struct packed { logic [3:0] hi; half_t lo; } pair_t;\n"
              "  box_t bx;\n"
              "  assign bx = v;\n"
              "  sequence s_r(logic [3:0] n, two_t [3:0] e, logic [8:1] w,\n"
              "               pk::w_t m, byte k, pair_t p);\n"
              "    n == 1 && e[3] == 3 && w[1] && m[1] && k[0] &&\n"
              "        p.hi == 0 && p.lo.b == 1 && p[0];\n"
              "  endsequence\n"
              "  sequence rule;\n"
              "    @(posedge clk) s_r(u, u, v[7:0], bx.f, v, {v[7:4], "
              "v[3:0]});\n"
              "  endsequence\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
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

// §16.8.1 (a) with §16.11: a parenthesized list of names, `(te1, note)`,
// bound to a formal of type sequence is the sequence it reads as, te1 with
// note called at its match, and not the event list it reads as too. With te1
// at ticks 2 and 5, note runs at the ticks at 15 and 45, whether or not te2
// follows; read as the event list, it never ran.
TEST(TypedSequenceFormals, AListOfNamesIsTheSequenceItReadsAs) {
  const std::string kPrelude =
      "  function void note;\n"
      "    $display(\"noted at %0t\", $time);\n"
      "  endfunction\n"
      "  sequence framed(sequence q);\n"
      "    q ##1 te2;\n"
      "  endsequence\n";
  SimFixture f;
  std::string out =
      RunCapture(SequenceTickSource("framed((te1, note))",
                                    DriveTicks({{2, 5}, {3}}), kPrelude),
                 f);
  EXPECT_EQ(out, "noted at 15\nnoted at 45\n$finish at time 160\n");
}

// §16.8.1 (a) with §16.12: a property whose body is the clocked boolean form,
// `@(posedge clk) q`, has its formal stand where a sequence_expr does, so a
// list of names bound to it, `(a, note)`, is the sequence it reads as. a is
// high at the posedges at 15 and 45, so the cover holds at both and note runs
// at both; read as the event list, `a or note`, note never ran.
TEST(TypedSequenceFormals, AClockedBooleanBodyTakesAListAsItsSequence) {
  SimFixture f;
  auto* notes = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0, a = 0;\n"
      "  int notes = 0, hits = 0;\n"
      "  function void note; notes++; endfunction\n"
      "  property p(q); @(posedge clk) q; endproperty\n"
      "  c1: cover property (p((a, note))) hits++;\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin\n"
      "    #12 a = 1; #10 a = 0; #20 a = 1; #10 a = 0; #20 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "notes");
  ASSERT_NE(notes, nullptr);
  EXPECT_EQ(notes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("hits")->value.ToUint64(), 2u);
}

}  // namespace
