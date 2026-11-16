#include <gtest/gtest.h>

#include <string>

#include "helpers_constraint_places.h"

using namespace delta;

namespace {

const char* const kAll = "16\n";
const char* const kFourSumTo40 =
    "o.q.size() == 4 && int'(o.q[0]) + o.q[1] + o.q[2] + o.q[3] == 40";
const char* const kSizeAndSum = "q.size == 4; q.sum() with (int'(item)) == 40;";

TEST(ArrayReductionCases, AQueueIsSizedBeforeItIsReduced) {
  EXPECT_EQ(Held(std::string("  rand bit [7:0] q[$];\n  constraint c { ") +
                     kSizeAndSum + " }\n",
                 kFourSumTo40),
            kAll);
}

TEST(ArrayReductionCases, AnInlineBlockSizesBeforeReducing) {
  EXPECT_EQ(HeldWith("  rand bit [7:0] q[];\n", kSizeAndSum, kFourSumTo40),
            kAll);
}

TEST(ArrayReductionCases, AReductionOnlyAnUnchosenSizeMeetsFails) {
  EXPECT_EQ(Fails("  rand bit [3:0] q[];\n"
                  "  constraint s { q.size inside {[1:2]}; }\n"
                  "  constraint c { q.sum() with (int'(item)) == 40; }\n"),
            kAll);
}

TEST(ArrayReductionCases, AnEmptyArraySumsToZero) {
  EXPECT_EQ(Held("  rand bit [3:0] q[];\n"
                 "  constraint s { q.size == 0; }\n"
                 "  constraint c { q.sum() with (int'(item)) == 0; }\n",
                 "o.q.size() == 0"),
            kAll);
  EXPECT_EQ(Fails("  rand bit [3:0] q[];\n"
                  "  constraint s { q.size == 0; }\n"
                  "  constraint c { q.sum() with (int'(item)) == 1; }\n"),
            kAll);
}

TEST(ArrayReductionCases, DISABLED_ASignedElementSumMayBeNegative) {
  EXPECT_EQ(Held("  rand byte a[3];\n"
                 "  constraint k { a.sum() == -6; }\n",
                 "byte'(o.a[0] + o.a[1] + o.a[2]) == -6"),
            kAll);
}

TEST(ArrayReductionCases, DISABLED_ASignedElementSumWrapsPast127) {
  EXPECT_EQ(Held("  rand byte a[2];\n"
                 "  constraint k { a[0] == 100; a[1] == 100; a.sum() < 0; }\n",
                 "o.a[0] == 100 && o.a[1] == 100"),
            kAll);
}

TEST(ArrayReductionCases, DISABLED_ASignedWithClauseOverUnsignedElements) {
  EXPECT_EQ(Held("  rand bit [7:0] a[2];\n"
                 "  constraint k { a[0] == 200; a[1] == 10; a.sum() with "
                 "(byte'(item)) == -46; }\n",
                 "o.a[0] == 200"),
            kAll);
}

TEST(ArrayReductionCases, DISABLED_AWithClauseNarrowerThanTheElement) {
  EXPECT_EQ(Held("  rand bit [7:0] a[2];\n"
                 "  constraint k { a[0] == 12; a[1] == 9; a.sum() with "
                 "(4'(item)) == 5; }\n",
                 "o.a[0] == 12"),
            kAll);
}

TEST(ArrayReductionCases, AndOrAndXorReduceFromSource) {
  EXPECT_EQ(Held("  rand bit [3:0] a[3];\n"
                 "  constraint k { a.and() == 4'hf; }\n",
                 "o.a[0] == 15 && o.a[1] == 15 && o.a[2] == 15"),
            kAll);
  EXPECT_EQ(Held("  rand bit [3:0] a[3];\n"
                 "  constraint k { a.or() == 0; }\n",
                 "o.a[0] == 0 && o.a[1] == 0 && o.a[2] == 0"),
            kAll);
  EXPECT_EQ(Held("  rand bit [3:0] a[3];\n"
                 "  constraint k { a[0] == 3; a[1] == 5; a.xor() == 4'hf; }\n",
                 "o.a[2] == 9"),
            kAll);
}

const char* const kAllFifteen = "o.a[0] == 15 && o.a[1] == 15 && o.a[2] == 15";
const char* const kSumTo45 = "a.sum() with (int'(item)) == 45;";

TEST(ArrayReductionCases, AQueueIsReduced) {
  EXPECT_EQ(Held(std::string("  rand bit [3:0] a[$];\n"
                             "  constraint c { a.size == 3; ") +
                     kSumTo45 + " }\n",
                 kAllFifteen),
            kAll);
}

TEST(ArrayReductionCases, AnAssociativeArrayIsReduced) {
  EXPECT_EQ(Held("  rand bit [3:0] a[int];\n"
                 "  constraint c { a.sum() with (int'(item)) == 30; }\n"
                 "  function new(); a[1] = 0; a[9] = 0; endfunction\n",
                 "o.a[1] == 15 && o.a[9] == 15"),
            kAll);
}

const char* const kGridAllFifteen =
    "o.m[0][0] == 15 && o.m[0][1] == 15 && o.m[1][0] == 15 && o.m[1][1] == "
    "15";

TEST(ArrayReductionCases, DISABLED_ATwoDimensionalArrayReducesThroughNesting) {
  EXPECT_EQ(Held("  rand bit [3:0] m[2][2];\n"
                 "  constraint k { m.sum() with (item.sum() with "
                 "(int'(item))) == 60; }\n",
                 kGridAllFifteen),
            kAll);
}

TEST(ArrayReductionCases, DISABLED_ARowIsReducedInsideAForeach) {
  EXPECT_EQ(Held("  rand bit [3:0] m[2][2];\n"
                 "  constraint k { foreach (m[i]) m[i].sum() with "
                 "(int'(item)) == 30; }\n",
                 kGridAllFifteen),
            kAll);
}

TEST(ArrayReductionCases, DISABLED_AWithClauseOverTheIndexIsReduced) {
  EXPECT_EQ(Held("  rand bit [3:0] a[3];\n"
                 "  constraint k { a.sum() with (int'(item.index)) == 3; "
                 "a[0] == 4; }\n",
                 "o.a[0] == 4"),
            kAll);
}

TEST(ArrayReductionCases, AWithClauseHoldingAConditionIsReduced) {
  EXPECT_EQ(Held("  rand bit [3:0] a[3];\n"
                 "  constraint k { a.sum() with (int'(item > 7)) == 3; }\n",
                 "o.a[0] > 7 && o.a[1] > 7 && o.a[2] > 7"),
            kAll);
}

TEST(ArrayReductionCases, AnInlineReductionHolds) {
  EXPECT_EQ(HeldWith("  rand bit [3:0] a[3];\n", kSumTo45, kAllFifteen), kAll);
}

TEST(ArrayReductionCases, AnOutOfBlockReductionHolds) {
  EXPECT_EQ(
      CountHeld(Tally("", "  rand bit [3:0] a[3];\n  constraint c;\n",
                      std::string("constraint C::c { ") + kSumTo45 + " }\n",
                      "o.randomize()", kAllFifteen)),
      kAll);
}

TEST(ArrayReductionCases, AScopeRandomizeReducesAStateArray) {
  EXPECT_EQ(HeldInScopeOf("  bit [3:0] st[3] = '{1, 2, 3};\n"
                          "  bit [3:0] x;\n",
                          "std::randomize(x) with { x == st.sum() with "
                          "(int'(item)); }",
                          "x == 6"),
            kAll);
}

TEST(ArrayReductionCases, DISABLED_AScopeRandomizeReducesTheArrayItDraws) {
  EXPECT_EQ(HeldInScopeOf("  bit [3:0] s[3];\n",
                          "std::randomize(s) with { s.sum() with (int'(item)) "
                          "== 45; }",
                          "s[0] == 15 && s[1] == 15 && s[2] == 15"),
            kAll);
}

}  // namespace
