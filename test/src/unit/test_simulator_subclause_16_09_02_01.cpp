#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_tick_bench.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SvaEngine, RepetitionZeroMin) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 0;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchRepetition(seq, {}));
  EXPECT_TRUE(MatchRepetition(seq, {1}));
  EXPECT_TRUE(MatchRepetition(seq, {1, 1}));
}

TEST(SvaEngine, EmptyConcatZeroDelayLeftNoMatch) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyLeft, 0);
  EXPECT_FALSE(r.matchable);
}

TEST(SvaEngine, EmptyConcatZeroDelayRightNoMatch) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyRight, 0);
  EXPECT_FALSE(r.matchable);
}

TEST(SvaEngine, EmptyConcatLeftCollapsesDelay) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyLeft, 2);
  EXPECT_TRUE(r.matchable);
  EXPECT_EQ(r.effective_delay, 1u);
  EXPECT_FALSE(r.append_true);
}

TEST(SvaEngine, EmptyConcatRightCollapsesDelayWithTrue) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyRight, 2);
  EXPECT_TRUE(r.matchable);
  EXPECT_EQ(r.effective_delay, 1u);
  EXPECT_TRUE(r.append_true);
}

TEST(SvaEngine, EmptyAtZeroDelayNeverMatchesButFusionDoes) {
  EXPECT_FALSE(ConcatEmptyMatch(EmptyConcatSide::kEmptyRight, 0).matchable);

  SvaSequence b;
  b.kind = SvaSequenceKind::kDelay;
  b.delay_cycles = 0;
  b.expr_check = [](uint64_t v) { return v == 1; };
  EXPECT_TRUE(MatchDelaySequence(b, {1}));
  EXPECT_FALSE(MatchDelaySequence(b, {0}));
}

TEST(SvaEngine, RangeAdmittingEmptyIsOrOfCases) {
  EXPECT_TRUE(MatchEmptyOrNonempty(0, true, false));
  EXPECT_TRUE(MatchEmptyOrNonempty(0, false, true));
  EXPECT_FALSE(MatchEmptyOrNonempty(0, false, false));

  EXPECT_FALSE(MatchEmptyOrNonempty(1, true, false));
  EXPECT_TRUE(MatchEmptyOrNonempty(1, false, true));
}

TEST(SvaEngine, EmptyConcatRightMinimalDelayStillAppendsTrue) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyRight, 1);
  EXPECT_TRUE(r.matchable);
  EXPECT_EQ(r.effective_delay, 0u);
  EXPECT_TRUE(r.append_true);
}

TEST(SvaEngine, RangeAdmittingEmptyBothCasesMatch) {
  EXPECT_TRUE(MatchEmptyOrNonempty(0, true, true));
}

TEST(SvaEngine, EmptyConcatLeftMinimalDelayDoesNotAppendTrue) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyLeft, 1);
  EXPECT_TRUE(r.matchable);
  EXPECT_EQ(r.effective_delay, 0u);
  EXPECT_FALSE(r.append_true);
}

std::string EmptyMatchSource(const std::string& body,
                             const std::string& drive) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic a = 0;\n"
         "  logic b = 0;\n"
         "  logic c = 0;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  sequence rule;\n"
         "    @(posedge clk) " +
         body +
         ";\n"
         "  endsequence\n"
         "  initial begin\n" +
         drive +
         "    #40 $finish;\n"
         "  end\n"
         "  initial forever begin\n"
         "    wait (rule.triggered);\n"
         "    hits = hits + 1;\n"
         "    last = $time;\n"
         "    @(posedge clk);\n"
         "  end\n"
         "endmodule\n";
}

const char* const kBThenAb =
    "    #10 b = 1;\n"
    "    #10 a = 1;\n"
    "    #10 a = 0; b = 0;\n";

TEST(EmptyMatchSequences, EmptyBeforeZeroDelayNeverMatches) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(EmptyMatchSource("a[*0] ##0 b", kBThenAb), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 0u);
  SimFixture g;
  auto* fused =
      RunAndFindVar(EmptyMatchSource("1'b1 ##0 b", kBThenAb), g, "hits");
  ASSERT_NE(fused, nullptr);
  EXPECT_EQ(fused->value.ToUint64(), 2u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

TEST(EmptyMatchSequences, EmptyAfterADelayCollapsesItByOne) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(EmptyMatchSource("b ##2 a[*0]", kBThenAb), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
  SimFixture g;
  auto* none =
      RunAndFindVar(EmptyMatchSource("b ##0 a[*0]", kBThenAb), g, "hits");
  ASSERT_NE(none, nullptr);
  EXPECT_EQ(none->value.ToUint64(), 0u);
}

TEST(EmptyMatchSequences, RangeAdmittingEmptyIsTheOrOfItsCases) {
  const char* const kTwoRounds =
      "    #10 b = 1;\n"
      "    #10 b = 0;\n"
      "    #10 c = 1;\n"
      "    #10 c = 0; b = 1;\n"
      "    #10 b = 0; a = 1;\n"
      "    #10 a = 0;\n"
      "    #10 c = 1;\n"
      "    #10 c = 0;\n";
  SimFixture f;
  auto* hits = RunAndFindVar(
      EmptyMatchSource("b ##1 a[*0:1] ##2 c", kTwoRounds), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 75u);
  SimFixture g;
  auto* spelled = RunAndFindVar(
      EmptyMatchSource("b ##2 c or b ##1 a ##2 c", kTwoRounds), g, "hits");
  ASSERT_NE(spelled, nullptr);
  EXPECT_EQ(spelled->value.ToUint64(), 2u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 75u);
}

struct EmptyRow {
  char how;
  const char* decls;
  const char* body;
  const char* ticks;
  const char* ends;
};

std::string ObservedItems(char how, const std::string& decls,
                          const std::string& body) {
  if (how == 'A') {
    return decls + "assert property (@(posedge clk) " + body +
           ") else $display(\"end %0t\", $time);";
  }
  if (how == 'C') {
    return decls + "cover sequence (@(posedge clk) " + body +
           ") $display(\"end %0t\", $time);";
  }
  return decls + "sequence rule; @(posedge clk) " + body +
         "; endsequence\n"
         "  initial forever begin\n"
         "    wait (rule.triggered);\n"
         "    $display(\"end %0t\", $time);\n"
         "    @(posedge clk);\n"
         "  end";
}

std::string RowEnds(char how, const std::string& decls, const std::string& body,
                    const std::string& ticks) {
  return TickLines("", ObservedItems(how, decls, body), TicksOf(ticks), "end ");
}

template <size_t N>
void ExpectRows(const EmptyRow (&rows)[N]) {
  for (const EmptyRow& row : rows) {
    SCOPED_TRACE(std::string(row.body) + " over " + row.ticks);
    EXPECT_EQ(RowEnds(row.how, row.decls, row.body, row.ticks), row.ends);
  }
}

const char kTwoA[] = "sequence two_a; a ##1 a; endsequence\n  ";

const char kS[] = "sequence s; a ##1 a; endsequence\n  ";

const EmptyRow kEmptyBeforeZeroDelay[] = {
    {'T', "", "(a ##1 a)[*0] ##0 b", "ab ab ab", ""},
    {'T', "", "1 ##0 b", "ab ab ab", "15 25 35"},
    {'T', "sequence e; a[*0]; endsequence\n  ", "e ##0 b", "ab ab ab", ""},
    {'T', "sequence s(x); x ##0 b; endsequence\n  ", "s(a[*0])", "ab ab ab",
     ""},
    {'T', "", "a[*0] ##0 b[*0]", "ab ab ab", ""},
    {'T', "", "a[*0:1] ##0 b", "b ab -", "25"},
    {'T', "", "a[*0:$] ##0 b", "b ab ab", "25 35"},
    {'T', "", "a[*0] ##[0:1] b", "b - b", "15 35"}};

TEST(EmptyMatchSequences, AnEmptyOperandBeforeZeroDelayGivesNoMatch) {
  ExpectRows(kEmptyBeforeZeroDelay);
}

const EmptyRow kEmptyAfterZeroDelay[] = {
    {'T', "", "b ##0 a[*0:0]", "b ab bc c", ""},
    {'T', "", "b ##1 a[*0:0]", "b ab bc c", "15 25 35"},
    {'T', "", "b ##0 (a ##1 a)[*0]", "b ab bc c", ""},
    {'T', "", "b ##1 (a ##1 a)[*0]", "b ab bc c", "15 25 35"},
    {'T', kTwoA, "b ##0 two_a[*0]", "b ab bc c", ""},
    {'T', kTwoA, "b ##1 two_a[*0]", "b ab bc c", "15 25 35"},
    {'T', "", "b ##1 c ##0 a[*0]", "b ab bc c", ""},
    {'T', "", "b ##1 c ##1 a[*0]", "b ab bc c", "35 45"},
    {'T', "", "a[*0] ##0 b[*0]", "b ab bc c", ""},
    {'T', "", "b ##1 a[*0] ##1 c", "b ab bc c", "35 45"},
    {'T', "", "a[*0] ##0 b[*0] ##1 c", "b ab bc c", ""}};

const EmptyRow kEmptyAfterZeroDelayThenMore[] = {
    {'T', "", "b ##0 a[*0] ##1 c", "b ab bc c", ""},
    {'T', "", "b ##0 a[*0] ##2 c", "b ab bc c", ""},
    {'T', "", "b ##0 (a ##1 a)[*0] ##1 c", "b ab bc c", ""}};

TEST(EmptyMatchSequences, AnEmptyOperandAfterZeroDelayGivesNoMatch) {
  ExpectRows(kEmptyAfterZeroDelay);
}

TEST(EmptyMatchSequences,
     DISABLED_AChainThroughAnEmptyOperandAfterZeroDelayNeverMatches) {
  ExpectRows(kEmptyAfterZeroDelayThenMore);
}

const EmptyRow kEmptyFirstShortensTheDelay[] = {
    {'A', "", "c |-> a[*0] ##1 b", "bc -", ""},
    {'A', "", "c |-> a[*0] ##1 b", "c b", "15"},
    {'A', "", "c |-> a[*0] ##2 b", "c b", ""},
    {'A', "", "c |-> a[*0] ##2 b", "c - b", "25"},
    {'A', "", "c |-> a[*0:1] ##2 b", "c b", ""},
    {'A', "", "c |-> a[*0:1] ##2 b", "c - b", "25"},
    {'A', "", "c |-> (a ##1 a)[*0] ##1 b", "abc a", ""},
    {'A', "", "c |-> (a ##1 a)[*0] ##1 b", "ac ab", "15"},
    {'A', "", "c |-> (a ##1 a)[*0] ##2 b", "ac ab", ""},
    {'A', "", "c |-> (a ##1 a)[*0] ##2 b", "ac a ab", "25"},
    {'A', kS, "c |-> s[*0] ##1 b", "abc a", ""},
    {'A', kS, "c |-> s[*0] ##1 b", "ac ab", "15"},
    {'A', kS, "c |-> s[*0] ##2 b", "ac ab", ""},
    {'A', kS, "c |-> s[*0] ##2 b", "ac a ab", "25"},
    {'T', "", "b ##1 a[*0] ##1 c", "b c - b - c", "25"},
    {'T', "", "b ##1 a[*0] ##2 c", "b c c c", "35"},
    {'T', "", "b ##1 (a ##1 a)[*0] ##2 c", "ab ac ac ac", "35"},
    {'T', kS, "b ##1 s[*0] ##1 c", "ab ac ac", "25"},
    {'T', kS, "b ##1 s[*0] ##2 c", "ab ac ac ac", "35"}};

TEST(EmptyMatchSequences, AnEmptyOperandBeforeADelayShortensItByOne) {
  ExpectRows(kEmptyFirstShortensTheDelay);
}

const EmptyRow kEmptyLastShortensTheDelay[] = {
    {'T', "", "b ##1 a[*0]", "b - -", "15"},
    {'T', "", "b ##1 a[*0]", "ab a a", "15"},
    {'T', "", "b ##3 a[*0]", "b - - - -", "35"},
    {'T', "", "b ##[1:2] a[*0]", "b - -", "15 25"},
    {'C', "", "b ##1 a[*0:1]", "b a", "15 25"},
    {'C', "", "b ##1 a[*0:1]", "b -", "15"},
    {'A', "", "b |=> a ##2 c[*0]", "b a -", ""},
    {'A', "", "b |=> a ##2 c[*0]", "b - -", "25"}};

TEST(EmptyMatchSequences, AnEmptyOperandAfterADelayShortensItByOne) {
  ExpectRows(kEmptyLastShortensTheDelay);
}

TEST(EmptyMatchSequences, TwoEmptyOperandsAcrossADelayMatchAtEveryTick) {
  const std::string kEvery = RowEnds('T', "", "1", "- -");
  EXPECT_NE(kEvery, "");
  EXPECT_EQ(RowEnds('T', "", "a[*0] ##2 c[*0]", "- -"), kEvery);
}

const EmptyRow kZeroCounts[] = {
    {'C', kS, "b ##1 s[*0] ##1 c", "ab ac a", "25"},
    {'C', "sequence t(y); y ##1 y; endsequence\n  ", "b ##1 t(a)[*0] ##1 c",
     "ab ac a", "25"},
    {'T', "localparam int N = 0;\n  ", "b ##1 a[*N] ##1 c", "b c", "25"},
    {'T', "", "b ##1 a[*0:0] ##1 c", "b c", "25"},
    {'T', "", "b ##1 a[*0:0] ##1 c", "b a c", ""}};

TEST(EmptyMatchSequences, AZeroCountOfAnyFormIsTheEmptySequence) {
  ExpectRows(kZeroCounts);
}

struct EmptyPlace {
  const char* place;
  const char* outside;
  const char* items;
};

const EmptyPlace kEmptyPlaces[] = {
    {"interface",
     "interface ifc(input logic clk, a, b);\n"
     "  sequence rule; @(posedge clk) @@; endsequence\n"
     "  cover sequence (rule) $display(\"end %0t\", $time);\n"
     "endinterface\n",
     "ifc i(clk, a, b);"},
    {"program",
     "program pg(input logic clk, a, b);\n"
     "  sequence rule; @(posedge clk) @@; endsequence\n"
     "  cover sequence (rule) $display(\"end %0t\", $time);\n"
     "endprogram\n",
     "pg p(clk, a, b);"},
    {"checker",
     "checker ck(logic clk, logic a, logic b);\n"
     "  sequence rule; @(posedge clk) @@; endsequence\n"
     "  cover sequence (rule) $display(\"end %0t\", $time);\n"
     "endchecker\n",
     "ck k(clk, a, b);"},
    {"package",
     "package pk;\n"
     "  sequence rule(clk, a, b); @(posedge clk) @@; endsequence\n"
     "endpackage\n",
     "cover sequence (pk::rule(clk, a, b)) $display(\"end %0t\", $time);"},
    {"generate block", "",
     "if (1) begin : g\n"
     "    sequence rule; @(posedge clk) @@; endsequence\n"
     "    cover sequence (rule) $display(\"end %0t\", $time);\n"
     "  end"},
    {"compilation unit",
     "sequence rule(clk, a, b); @(posedge clk) @@; endsequence\n",
     "cover sequence (rule(clk, a, b)) $display(\"end %0t\", $time);"}};

std::string PlacedEnds(const EmptyPlace& placed, const std::string& body) {
  auto fill = [&](std::string text) {
    size_t at = text.find("@@");
    if (at != std::string::npos) text.replace(at, 2, body);
    return text;
  };
  return TickLines(fill(placed.outside), fill(placed.items), TicksOf("b ab b"),
                   "end ");
}

void ExpectEmptyBeforeZeroDelayIn(const char* place) {
  for (const auto& placed : kEmptyPlaces) {
    if (std::string(placed.place) != place) continue;
    SCOPED_TRACE(place);
    EXPECT_EQ(PlacedEnds(placed, "(a[*0] ##0 b) or (b ##1 1)"), "25 35 45");
    EXPECT_EQ(PlacedEnds(placed, "(1 ##0 b) or (b ##1 1)"),
              "15 25 25 35 35 45");
  }
}

TEST(EmptyMatchSequences, AnEmptyOperandBeforeZeroDelayGivesNoMatchAnywhere) {
  for (const char* place :
       {"interface", "program", "checker", "package", "generate block"}) {
    ExpectEmptyBeforeZeroDelayIn(place);
  }
}

TEST(EmptyMatchSequences, DISABLED_AnEmptyOperandBeforeZeroDelayInTheUnit) {
  ExpectEmptyBeforeZeroDelayIn("compilation unit");
}

}  // namespace
