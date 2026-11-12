#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_sequence_ticks.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

TEST(TypedSequenceFormals, AKeywordTypeWrittenWithASigningCastsToIt) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      TypedSource("  sequence s_g(byte unsigned b, int unsigned i,\n"
                  "               logic signed g);\n"
                  "    b == 254 && i > 0 && g < 0;\n"
                  "  endsequence\n"
                  "  sequence rule;\n"
                  "    @(posedge clk) s_g(~v, v - 2, v);\n"
                  "  endsequence\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

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

TEST(TypedSequenceFormals, ABooleanActualMatchesInsideTheBodyAroundIt) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource("framed(te2)", DriveTicks({{1}, {2}, {2}}),
                         "  sequence framed(sequence q);\n"
                         "    te1 ##1 q;\n"
                         "  endsequence\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 15u);
}

void ExpectConvertedOnce(const std::string& formal, const std::string& body,
                         const std::string& actual) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(TypedSource("  sequence sc(" + formal + ");\n    " + body +
                                ";\n"
                                "  endsequence\n"
                                "  sequence rule;\n"
                                "    @(posedge clk) v[1] ##0 sc(" +
                                actual + ");\n  endsequence\n"),
                    f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 15u);
}

TEST(TypedSequenceFormals, ARealActualRoundsToAnIntegralFormal) {
  ExpectConvertedOnce("int k", "k == 3", "2.6");
}

TEST(TypedSequenceFormals, DISABLED_AnIntegralActualBecomesARealFormal) {
  ExpectConvertedOnce("real h", "h / 4 == 0.5", "2");
}

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
