#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive the distribution operator (18.5.3) end to end: each source
// program declares a class with an "expression dist { dist_list }" constraint,
// calls randomize() from an initial block, and copies results out to module
// variables the harness reads. The parser captures the dist form and the
// simulator builds it into a weighted-value (kDist) solver constraint, so the
// behavior observed here is that of real elaborated source, not a hand-built
// solver state. Because a distribution weights values probabilistically, the
// weighting rules are observed by drawing many samples in a source loop and
// comparing how often each value appears; the object's RNG advances on every
// randomize() call, so a loop yields a spread of draws. The membership and
// error rules are observed from a single, deterministic randomize() call.

// 18.5.3: the dist operator is a relational test for set membership — only a
// value named by the dist set is ever produced. A set naming the single value
// 42 pins x to 42 on every solve.
TEST(ConstraintDist, OnlyListedValueProduced) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {42 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 42u);
}

// 18.5.3: the set membership admits a value_range element, not only single
// values. A distribution whose only item is the range [100:110] confines x to
// that range on every solve, so no value outside it is ever produced.
TEST(ConstraintDist, RangeElementRestrictsMembershipToRange) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[100:110] := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int inrange;\n"
      "  int outrange;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    inrange = 0;\n"
      "    outrange = 0;\n"
      "    for (int i = 0; i < 200; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x >= 100 && o.x <= 110) inrange = inrange + 1;\n"
      "      else outrange = outrange + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "inrange"), 200u);
  EXPECT_EQ(RunAndGet(src, "outrange"), 0u);
}

// 18.5.3: a value whose total weight across the distribution is zero is treated
// as a constraint that x not take that value. With 17 weighted zero and named
// by no other item, only 42 is reachable, so every solve yields 42.
TEST(ConstraintDist, ZeroTotalWeightValueExcluded) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {17 := 0, 42 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    void'(o.randomize());\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 42u);
}

// 18.5.3: absent any other constraints, the probability that x matches an item
// is proportional to the item's weight. A 1000:1 ratio drives nearly every
// sample to the heavily weighted value.
TEST(ConstraintDist, ProbabilityProportionalToWeight) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {10 := 1000, 20 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int c10;\n"
      "  int c20;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    c10 = 0;\n"
      "    c20 = 0;\n"
      "    for (int i = 0; i < 200; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 10) c10 = c10 + 1;\n"
      "      if (o.x == 20) c20 = c20 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "c10"), 150u);
  EXPECT_LT(RunAndGet(src, "c20"), 50u);
}

// 18.5.3: an integral item with no weight specified takes a default weight
// of 1. Here 10 is given no weight and 20 is given weight 1, so the two occur
// with comparable frequency.
TEST(ConstraintDist, AbsentWeightDefaultsToOne) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {10, 20 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int c10;\n"
      "  int c20;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    c10 = 0;\n"
      "    c20 = 0;\n"
      "    for (int i = 0; i < 300; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 10) c10 = c10 + 1;\n"
      "      if (o.x == 20) c20 = c20 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "c10"), 80u);
  EXPECT_GT(RunAndGet(src, "c20"), 80u);
}

// 18.5.3: the default weight of 1 for an item with no explicit weight applies
// to a range item too, and the default is the := (per-element) form rather than
// :/. A bare range [1:4] therefore carries a total weight equal to its four
// elements, so it is about four times as likely overall as a bare single value
// — had the default been :/ (whole-range) the two would be equally likely.
TEST(ConstraintDist, AbsentWeightOnRangeIsPerElementDefault) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[1:4], 100}; }\n"
      "endclass\n"
      "module t;\n"
      "  int inr;\n"
      "  int at100;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    inr = 0;\n"
      "    at100 = 0;\n"
      "    for (int i = 0; i < 400; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x >= 1 && o.x <= 4) inr = inr + 1;\n"
      "      if (o.x == 100) at100 = at100 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  // Expected ratio 4:1; the range should dominate by a clear margin.
  EXPECT_GT(RunAndGet(src, "inr"), RunAndGet(src, "at100") * 2);
}

// 18.5.3: the weight is interpreted as an unsigned value. A weight written as
// -1 — a negative number if read as signed — is honoured as a large positive
// magnitude, so the value carrying it overwhelms a value weighted 1.
TEST(ConstraintDist, WeightInterpretedAsUnsigned) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {10 := -1, 20 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int c10;\n"
      "  int c20;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    c10 = 0;\n"
      "    c20 = 0;\n"
      "    for (int i = 0; i < 200; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 10) c10 = c10 + 1;\n"
      "      if (o.x == 20) c20 = c20 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "c10"), 195u);
  EXPECT_LT(RunAndGet(src, "c20"), 5u);
}

// 18.5.3: when := is applied to a range the weight is assigned to each element,
// so the range's total weight is its element count times the per-element
// weight. A four-element range weighted 1 is about four times as likely overall
// as a single value weighted 1.
TEST(ConstraintDist, AssignWeightOnRangeIsPerElement) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[1:4] := 1, 100 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int inr;\n"
      "  int at100;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    inr = 0;\n"
      "    at100 = 0;\n"
      "    for (int i = 0; i < 400; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x >= 1 && o.x <= 4) inr = inr + 1;\n"
      "      if (o.x == 100) at100 = at100 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  // Expected ratio 4:1; require the range to dominate by a clear margin.
  EXPECT_GT(RunAndGet(src, "inr"), RunAndGet(src, "at100") * 2);
}

// 18.5.3: when :/ is applied to a range the weight is assigned to the range as
// a whole, so the same four-element range weighted 1 is only as likely overall
// as a single value weighted 1.
TEST(ConstraintDist, DivideWeightOnRangeIsWholeRange) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[1:4] :/ 1, 100 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int inr;\n"
      "  int at100;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    inr = 0;\n"
      "    at100 = 0;\n"
      "    for (int i = 0; i < 400; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x >= 1 && o.x <= 4) inr = inr + 1;\n"
      "      if (o.x == 100) at100 = at100 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  // Expected ratio 1:1; both outcomes should be of comparable frequency.
  uint64_t inr = RunAndGet(src, "inr");
  uint64_t at100 = RunAndGet(src, "at100");
  EXPECT_GT(inr, at100 / 2);
  EXPECT_GT(at100, inr / 2);
}

// 18.5.3: the := and :/ operators assign the specified weight to an individual
// value identically — the per-element distinction governs only ranges. Two
// classes differing solely in which operator tags the same single-value set
// draw the same sequence from the same object seed, so their outcome counts
// match exactly.
TEST(ConstraintDist, AssignAndDivideEquivalentForSingleValues) {
  const char* assign_src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {100 := 1, 200 := 2}; }\n"
      "endclass\n"
      "module t;\n"
      "  int c100;\n"
      "  int c200;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    c100 = 0;\n"
      "    c200 = 0;\n"
      "    for (int i = 0; i < 200; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 100) c100 = c100 + 1;\n"
      "      if (o.x == 200) c200 = c200 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  const char* divide_src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {100 :/ 1, 200 :/ 2}; }\n"
      "endclass\n"
      "module t;\n"
      "  int c100;\n"
      "  int c200;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    c100 = 0;\n"
      "    c200 = 0;\n"
      "    for (int i = 0; i < 200; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 100) c100 = c100 + 1;\n"
      "      if (o.x == 200) c200 = c200 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(assign_src, "c100"), RunAndGet(divide_src, "c100"));
  EXPECT_EQ(RunAndGet(assign_src, "c200"), RunAndGet(divide_src, "c200"));
}

// 18.5.3: if a single value occurs in multiple items, the weights allocated to
// that value are additive. Value 200 appears in two weight-1 items and so is
// about twice as likely as the single weight-1 value 100.
TEST(ConstraintDist, WeightsAreAdditiveAcrossItems) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {100 := 1, 200 := 1, 200 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int c100;\n"
      "  int c200;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    c100 = 0;\n"
      "    c200 = 0;\n"
      "    for (int i = 0; i < 300; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 100) c100 = c100 + 1;\n"
      "      if (o.x == 200) c200 = c200 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "c200"), RunAndGet(src, "c100"));
}

// 18.5.3: the additive behavior includes items explicitly weighted to zero. The
// 50:=0 item does not exclude 50 because 50 is also covered by a nonzero range
// item, so both 50 and 51 remain reachable and no other value appears.
TEST(ConstraintDist, ZeroWeightItemDoesNotConstrainWhenCoveredElsewhere) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {50 := 0, [50:51] := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int c50;\n"
      "  int other;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    c50 = 0;\n"
      "    other = 0;\n"
      "    for (int i = 0; i < 200; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 50) c50 = c50 + 1;\n"
      "      if (o.x != 50 && o.x != 51) other = other + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "c50"), 0u);
  EXPECT_EQ(RunAndGet(src, "other"), 0u);
}

// 18.5.3: nonzero distribution weights do not remove values from the solution
// space. Even weighted 100 times more lightly, value 20 is still reachable
// across many randomizations.
TEST(ConstraintDist, NonzeroWeightDoesNotExcludeValue) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {10 := 100, 20 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int c20;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    c20 = 0;\n"
      "    for (int i = 0; i < 1500; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 20) c20 = c20 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "c20"), 0u);
}

// 18.5.3: the default specification stands for every value of the domain not
// present in any other item. With 0 named explicitly and everything else
// covered by default, both 0 and some nonzero value are produced across many
// solves.
TEST(ConstraintDist, DefaultCoversRemainderOfDomain) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {0 := 1, default :/ 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int czero;\n"
      "  int cother;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    czero = 0;\n"
      "    cother = 0;\n"
      "    for (int i = 0; i < 100; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 0) czero = czero + 1;\n"
      "      if (o.x != 0) cother = cother + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "czero"), 0u);
  EXPECT_GT(RunAndGet(src, "cother"), 0u);
}

// 18.5.3: a dist operation shall not be applied to a randc variable, so a
// distribution targeting one makes randomize() fail.
TEST(ConstraintDist, DistOnRandcVariableFails) {
  const char* src =
      "class C;\n"
      "  randc int x;\n"
      "  constraint c { x dist {10 := 1, 20 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

// 18.5.3: a dist expression requires that the expression contain at least one
// rand variable. A distribution applied to a non-rand member supplies no rand
// variable, so randomize() fails even though the class has an unrelated rand
// member.
TEST(ConstraintDist, DistRequiresRandVariableFails) {
  const char* src =
      "class C;\n"
      "  rand int y;\n"
      "  int x;\n"
      "  constraint c { x dist {10 := 1, 20 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

}  // namespace
