#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Runs a two-alternative na/nb randsequence trial `iterations` times. The
// `main_rule` parameter is the body of the `main :` production (everything
// between "main : " and the trailing ';'), letting each test vary only the
// weight grammar while sharing the module, loop, lowering, and run sequence.
// The resulting na/nb counts are returned via out-parameters.
void RunNaNbTrial(SimFixture& f, std::string_view main_rule, int iterations,
                  uint64_t& na_count, uint64_t& nb_count) {
  std::string src =
      "module t;\n"
      "  logic [31:0] na, nb;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    na = 0; nb = 0;\n"
      "    for (i = 0; i < " +
      std::to_string(iterations) +
      "; i = i + 1)\n"
      "      randsequence(main)\n"
      "        main : " +
      std::string(main_rule) +
      ";\n"
      "        a : { na = na + 1; };\n"
      "        b : { nb = nb + 1; };\n"
      "      endsequence\n"
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* na = f.ctx.FindVariable("na");
  auto* nb = f.ctx.FindVariable("nb");
  ASSERT_NE(na, nullptr);
  ASSERT_NE(nb, nullptr);
  na_count = na->value.ToUint64();
  nb_count = nb->value.ToUint64();
}

// §18.17.1 claim 1: the probability of selecting a production list is
// proportional to its specified weight. With weights 3:1 over many trials the
// heavier alternative is generated substantially more often, while both remain
// reachable.
TEST(RandsequenceSim, ProbabilityProportionalToWeight) {
  SimFixture f;
  uint64_t na = 0, nb = 0;
  RunNaNbTrial(f, "a := 3 | b := 1", 200, na, nb);

  // Every trial picks exactly one alternative.
  EXPECT_EQ(na + nb, 200u);
  // Both alternatives are reachable, and the weight-3 list dominates the
  // weight-1 list (expected 150 vs 50).
  EXPECT_GT(na, 0u);
  EXPECT_GT(nb, 0u);
  EXPECT_GT(na, nb);
}

// §18.17.1 claim 1 (extreme): a production list whose weight evaluates to zero
// is never generated; selection probability proportional to weight makes a
// zero weight unreachable.
TEST(RandsequenceSim, ZeroWeightProductionListNeverSelected) {
  SimFixture f;
  uint64_t na = 0, nb = 0;
  RunNaNbTrial(f, "a := 0 | b := 1", 50, na, nb);

  EXPECT_EQ(na, 0u);
  EXPECT_EQ(nb, 50u);
}

// §18.17.1 claims 6 & 7: a production list with no specified weight uses a
// weight of 1. Here 'a' has no weight (defaults to 1) and 'b' is given weight
// 0, so 'a' is always selected — demonstrating the unspecified weight is the
// nonzero default of 1 rather than 0.
TEST(RandsequenceSim, UnspecifiedWeightDefaultsToOne) {
  SimFixture f;
  uint64_t na = 0, nb = 0;
  RunNaNbTrial(f, "a | b := 0", 50, na, nb);

  EXPECT_EQ(na, 50u);
  EXPECT_EQ(nb, 0u);
}

// §18.17.1 claims 2, 3 & 5: the ':=' weight may be an expression that evaluates
// to an integral value, and the weight is evaluated when its enclosing
// production is selected (allowing weights to change dynamically). The same
// grammar shape yields different selections because the weight expression reads
// the current value of 'g': with g=1 the first list wins, with g=0 the second.
TEST(RandsequenceSim, WeightEvaluatedDynamicallyFromExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic g;\n"
      "  logic [7:0] x1, x2;\n"
      "  initial begin\n"
      "    g = 1'b1;\n"
      "    randsequence(m1)\n"
      "      m1 : p := g | q := (1'b1 - g);\n"
      "      p : { x1 = 8'd1; };\n"
      "      q : { x1 = 8'd2; };\n"
      "    endsequence\n"
      "    g = 1'b0;\n"
      "    randsequence(m2)\n"
      "      m2 : r := g | s := (1'b1 - g);\n"
      "      r : { x2 = 8'd1; };\n"
      "      s : { x2 = 8'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x1 = f.ctx.FindVariable("x1");
  auto* x2 = f.ctx.FindVariable("x2");
  ASSERT_NE(x1, nullptr);
  ASSERT_NE(x2, nullptr);

  // g=1: weights are 1 vs 0 -> first list 'p'.
  EXPECT_EQ(x1->value.ToUint64(), 1u);
  // g=0: weights are 0 vs 1 -> second list 's'.
  EXPECT_EQ(x2->value.ToUint64(), 2u);
}

// §18.17.1 claims 6 & 7: the unspecified weight is not merely nonzero — it is
// exactly 1. Pitting an unspecified alternative against an explicit weight of 3
// yields an effective 1:3 split, so the explicit list is generated about three
// times as often. The expected counts (~50 vs ~150) make nb exceed twice na,
// which would fail if the default were 2 or larger (~80 vs ~120), pinning the
// implied default to 1.
TEST(RandsequenceSim, DefaultWeightOfOneRelativeToExplicit) {
  SimFixture f;
  uint64_t na = 0, nb = 0;
  RunNaNbTrial(f, "a | b := 3", 200, na, nb);

  EXPECT_EQ(na + nb, 200u);
  EXPECT_GT(na, 0u);
  EXPECT_GT(nb, 0u);
  // 1:3 split -> nb is roughly triple na, comfortably above 2x.
  EXPECT_GT(nb, 2u * na);
}

// §18.17.1 claim 5 (edge case): a weight is only meaningful when assigned to
// alternative production lists separated by '|'. A production with a single
// list has no alternatives, so its weight is inconsequential — even a weight of
// 0, which would make a list unreachable when competing against alternatives
// (see ZeroWeightProductionListNeverSelected), leaves the lone list generated
// every time. This exercises the single-list short circuit in SelectRule, which
// returns the only list before the weight is consulted.
TEST(RandsequenceSim, WeightOnNonAlternativeProductionIsIgnored) {
  SimFixture f;
  auto* na = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] na;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    na = 0;\n"
      "    for (i = 0; i < 50; i = i + 1)\n"
      "      randsequence(main)\n"
      "        main : a := 0;\n"
      "        a : { na = na + 1; };\n"
      "      endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "na");
  ASSERT_NE(na, nullptr);

  // Despite the zero weight, the sole production list is always generated.
  EXPECT_EQ(na->value.ToUint64(), 50u);
}

// §18.17.1 claims 2 & 3, ps_identifier weight form: the weight may be a
// ps_identifier that names an elaboration-time parameter. Resolving a parameter
// as the weight takes the parameter-lookup path in expression evaluation rather
// than a plain variable read, yet the selector must apply the resolved value as
// the production-list weight all the same. With parameters 1 and 0 the weight-1
// list is always chosen and the weight-0 list never, so the observed outcome
// pins the parameter values as the applied weights.
TEST(RandsequenceSim, ParameterWeightSelectsProductionList) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  parameter WA = 1;\n"
      "  parameter WB = 0;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    randsequence(main)\n"
      "      main : a := WA | b := WB;\n"
      "      a : { x = 8'd1; };\n"
      "      b : { x = 8'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  // WA=1 outweighs WB=0, so list 'a' is generated.
  EXPECT_EQ(x->value.ToUint64(), 1u);
}

// §18.17.1 claims 2 & 3, ps_identifier weight form: the ps_identifier weight
// also admits a localparam, a distinct constant form of 11.2.1. Here the two
// weights are localparams 0 and 1 in that order, so the SECOND alternative
// wins. Reversing the winner relative to the parameter test confirms selection
// follows the localparam values rather than the syntactic order of the lists.
TEST(RandsequenceSim, LocalparamWeightSelectsProductionList) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  localparam LA = 0;\n"
      "  localparam LB = 1;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    randsequence(main)\n"
      "      main : a := LA | b := LB;\n"
      "      a : { x = 8'd1; };\n"
      "      b : { x = 8'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  // LB=1 outweighs LA=0, so list 'b' is generated.
  EXPECT_EQ(x->value.ToUint64(), 2u);
}

// §18.17.1, printed page 567, the sentence standing between claims 5 and 6
// above: "Weight expressions are evaluated when their enclosing production is
// selected, thus allowing weights to change dynamically." One selection of a
// production evaluates each of its rules' weights once, so a weight whose
// evaluation has an effect performs that effect once per rule.
// rs_weight_specification admits a parenthesized expression and so a function
// call: each of the three alternatives here weighs (bump()), a call that
// advances `cnt` and returns 1, and one generation of `main` leaves cnt at 3 —
// one evaluation per rule. A literal weight cannot make this claim, because it
// reads the same number whether it is evaluated once or twice; the counter is
// what separates one evaluation from two.
TEST(RandsequenceSim, WeightExpressionEvaluatedOncePerSelection) {
  SimFixture f;
  auto* cnt = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] cnt;\n"
      "  logic [7:0] x;\n"
      "  function int bump();\n"
      "    cnt = cnt + 1;\n"
      "    return 1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    cnt = 0;\n"
      "    x = 0;\n"
      "    randsequence(main)\n"
      "      main : a := (bump()) | b := (bump()) | c := (bump());\n"
      "      a : { x = 8'd1; };\n"
      "      b : { x = 8'd2; };\n"
      "      c : { x = 8'd3; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "cnt");
  ASSERT_NE(cnt, nullptr);
  // Three rules, three weight evaluations.
  EXPECT_EQ(cnt->value.ToUint64(), 3u);
  // One of the three alternatives was generated, so the count above was reached
  // by selecting rather than by never running the statement.
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_GE(x->value.ToUint64(), 1u);
  EXPECT_LE(x->value.ToUint64(), 3u);
}

// §18.17.1, printed page 567, the same sentence: the weights a selection is
// drawn against are the weights that selection is made from, because each is
// evaluated once.
// Rule 'a' weighs (w++), which reads w and increments it, so with w starting at
// 0 that weight is 0 and rule 'b' weighs the literal 1. §18.17.1 makes a
// zero-weight list unreachable (see ZeroWeightProductionListNeverSelected), so
// 'b' is generated and x is 2.
//
// The outcome does not depend on the random draw. The weights sum to 1, so the
// selector's draw modulo the total is 0 for every random number, and it does
// not depend on the order the two weights are evaluated in either, since only
// 'a' reads or writes w. Evaluating the weights a second time to walk them
// makes 'a' weigh 1 on that second read, and 'a' then covers the whole [0, 1)
// interval the draw landed in, selecting the alternative §18.17.1 rules out.
TEST(RandsequenceSim, WeightReadingItsOwnIncrementSelectsFromTheSummedWeights) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  int unsigned w;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    w = 0;\n"
      "    x = 0;\n"
      "    randsequence(main)\n"
      "      main : a := (w++) | b := 1;\n"
      "      a : { x = 8'd1; };\n"
      "      b : { x = 8'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  // Weights 0 and 1: the zero-weight list is unreachable and 'b' is generated.
  EXPECT_EQ(x->value.ToUint64(), 2u);
}

// The source RunWeightOnce writes, with `main_rule` as the whole of the
// production list. The weight stands on line 6 of it whatever the rule says,
// which is the line the reports below name. One iteration rather than the many
// RunNaNbTrial runs, because a weight the run reports is reported once per
// evaluation and a loop would say nothing a single pass does not.
void RunWeightOnce(SimFixture& f, std::string_view main_rule) {
  std::string src =
      "module t;\n"
      "  logic [31:0] na, nb;\n"
      "  initial begin\n"
      "    na = 0; nb = 0;\n"
      "    randsequence(main)\n"
      "      main : " +
      std::string(main_rule) +
      ";\n"
      "      a : { na = na + 1; };\n"
      "      b : { nb = nb + 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
}

// §18.17.1: "an rs_weight_specification shall evaluate to an integral
// non-negative value". A negative one was read through ToUint64 as its
// two's-complement value, so this rule carried a weight of
// 18446744073709551615, `b` could not be reached, and the total then wrapped to
// zero and the first rule was returned outright. Nothing said so.
//
// The weight is parenthesized because Syntax 18-14 writes
// `rs_weight_specification ::= integral_number | ps_identifier | ( expression
// )`, and -1 is an expression rather than an integral_number. Two rules,
// because SelectRule returns a lone rule without evaluating its weight at all.
TEST(RandsequenceSim, NegativeWeightIsReported) {
  SimFixture f;
  RunWeightOnce(f, "a := (-1) | b := 1");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "randsequence rule weight shall evaluate to an "
                            "integral non-negative value",
                            6, "18.17.1"));
}

// An unknown value is not an integral non-negative value either, and it reaches
// the same site by a different route: ToUint64 reads x and z alike as 0, so
// such a weight was already a weight of zero and its rule was simply never
// selected. It is written as an integral_number, which is the form Syntax 18-14
// admits without parentheses.
TEST(RandsequenceSim, UnknownWeightIsReported) {
  SimFixture f;
  RunWeightOnce(f, "a := 1'bx | b := 1");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "randsequence rule weight shall evaluate to an "
                            "integral non-negative value",
                            6, "18.17.1"));
}

// Runs `main_rule` `iterations` times over three counted productions and
// reports how often each was generated. The seeded fixture makes the draw
// repeatable, so a case asserting a distribution asserts the same one on every
// run. `c` is declared whether the rule names it or not, an unnamed production
// simply never generating.
void RunAbcTrial(SimFixtureSeeded& f, std::string_view main_rule,
                 int iterations, std::vector<uint64_t>& counts) {
  std::string src =
      "module t;\n"
      "  logic [31:0] na, nb, nc;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    na = 0; nb = 0; nc = 0;\n"
      "    for (i = 0; i < " +
      std::to_string(iterations) +
      "; i = i + 1)\n"
      "      randsequence(main)\n"
      "        main : " +
      std::string(main_rule) +
      ";\n"
      "        a : { na = na + 1; };\n"
      "        b : { nb = nb + 1; };\n"
      "        c : { nc = nc + 1; };\n"
      "      endsequence\n"
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  for (const char* name : {"na", "nb", "nc"}) {
    auto* var = f.ctx.FindVariable(name);
    ASSERT_NE(var, nullptr);
    counts.push_back(var->value.ToUint64());
  }
}

// §18.17.1: "the probability that a particular production list is generated is
// proportional to its specified weight". SelectRule drew a single Urandom32
// against a 64-bit total, so the drawn number never reached 2^32 and every rule
// whose cumulative interval began at or beyond that was unreachable.
//
// Two rules of 2^32 each put the boundary exactly at the end of the first, so a
// narrow draw lands in the first every time and b is selected with probability
// zero. Both counts are asserted rather than b's alone, so a fix that always
// answered the last rule would not pass either. A total under 2^32 makes the
// narrow and the wide draw the same draw and cannot fail.
TEST(RandsequenceSim, WeightsSummingPastThirtyTwoBitsReachEveryRule) {
  SimFixtureSeeded f;
  std::vector<uint64_t> counts;
  RunAbcTrial(f, "a := 64'h1_0000_0000 | b := 64'h1_0000_0000", 40, counts);
  EXPECT_GT(counts[0], 0u);
  EXPECT_GT(counts[1], 0u);
}

// The same rule for an interval that begins two whole 2^32 blocks along, which
// the case above cannot show: a fix widening the draw by one bit would let b be
// reached and leave c as unreachable as before. Every rule of the three carries
// the same weight, so each is generated about a third of the time.
TEST(RandsequenceSim, AThirdRuleBeyondTwoBlocksIsStillReachable) {
  SimFixtureSeeded f;
  std::vector<uint64_t> counts;
  RunAbcTrial(
      f, "a := 64'h1_0000_0000 | b := 64'h1_0000_0000 | c := 64'h1_0000_0000",
      60, counts);
  EXPECT_GT(counts[0], 0u);
  EXPECT_GT(counts[2], 0u);
}

}  // namespace
