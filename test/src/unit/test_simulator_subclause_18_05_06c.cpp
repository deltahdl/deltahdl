#include <gtest/gtest.h>

#include "helpers_constraint_places.h"

using namespace delta;

namespace {

const char* const kDangling =
    "a == 9; b == 1; if (a > 7) if (b > 7) c == 1; else c == 2;";
const char* const kBracedOuter =
    "a == 1; b == 9; if (a > 7) { if (b > 7) c == 1; } else c == 2;";
const char* const kCIsTwo = "o.c == 2";

TEST(IfElseCases, TheDanglingElseBindsInnerInline) {
  EXPECT_EQ(CountHeld(HeldInline(kDangling, kCIsTwo)), "32\n");
}

TEST(IfElseCases, TheDanglingElseBindsInnerInAScopeRandomize) {
  EXPECT_EQ(CountHeld(HeldInScope(kDangling, kCIsTwo)), "32\n");
}

TEST(IfElseCases, TheDanglingElseBindsInnerOutOfBlock) {
  EXPECT_EQ(CountHeld(HeldOutOfBlock(kDangling, kCIsTwo)), "32\n");
}

TEST(IfElseCases, BracesBindTheElseToTheOuterIf) {
  EXPECT_EQ(CountHeld(HeldInClass(kBracedOuter, kCIsTwo)), "32\n");
  EXPECT_EQ(CountHeld(HeldInline(kBracedOuter, kCIsTwo)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kBracedOuter, kCIsTwo)), "32\n");
}

const char* const kThen = "a == 9; if (a > 7) b == 1; else b == 2;";
const char* const kElse = "a == 2; if (a > 7) b == 1; else b == 2;";
const char* const kRealThen = "r == 2.5; if (r > 1.0) b == 1; else b == 2;";
const char* const kRealElse = "r == 0.5; if (r > 1.0) b == 1; else b == 2;";
const char* const kBIsOne = "o.b == 1";
const char* const kBIsTwo = "o.b == 2";

TEST(IfElseCases, AnInlineElseBranchHolds) {
  EXPECT_EQ(CountHeld(HeldInline(kElse, kBIsTwo)), "32\n");
}

TEST(IfElseCases, AnInlineSetConstrainsTheCondition) {
  EXPECT_EQ(CountHeld(HeldInline("if (a > 7) b == 1; else b == 2; b == 1;",
                                 "o.a > 7")),
            "32\n");
}

TEST(IfElseCases, AScopeRandomizeSelectsEachBranch) {
  EXPECT_EQ(CountHeld(HeldInScope(kThen, kBIsOne)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kElse, kBIsTwo)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kRealThen, kBIsOne)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kRealElse, kBIsTwo)), "32\n");
}

TEST(IfElseCases, AnOutOfBlockIfElseSelectsEachBranch) {
  EXPECT_EQ(CountHeld(HeldOutOfBlock(kThen, kBIsOne)), "32\n");
  EXPECT_EQ(CountHeld(HeldOutOfBlock(kElse, kBIsTwo)), "32\n");
}

const char* const kNestedIf =
    "a == 9; b == 9; if (a > 7) { if (b > 7) c == 3; }";
const char* const kBranchImplication =
    "a == 9; b == 9; if (a > 7) b > 7 -> c == 3;";
const char* const kCIsThree = "o.c == 3";
const char* const kBranchForeach = "if (g) foreach (u[i]) u[i] == 2;";
const char* const kAllTwo =
    "o.u[0] == 2 && o.u[1] == 2 && o.u[2] == 2 && o.u[3] == 2";
const char* const kBranchUnique = "if (g) unique {u};";
const char* const kPermutation =
    "o.u[0] != o.u[1] && o.u[0] != o.u[2] && o.u[0] != o.u[3] && o.u[1] != "
    "o.u[2] && o.u[1] != o.u[3] && o.u[2] != o.u[3]";
const char* const kThenDist = "if (g) a dist {7 := 1}; else a dist {3 := 1};";
const char* const kElseDist = "if (!g) a dist {3 := 1}; else a dist {7 := 1};";
const char* const kBranchSoft = "if (g) soft a == 7;";
const char* const kAIsSeven = "o.a == 7";

TEST(IfElseCases, ANestedIfInABracedThenSetHolds) {
  EXPECT_EQ(CountHeld(HeldInClass(kNestedIf, kCIsThree)), "32\n");
  EXPECT_EQ(CountHeld(HeldInline(kNestedIf, kCIsThree)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kNestedIf, kCIsThree)), "32\n");
}

TEST(IfElseCases, AnImplicationInABranchHolds) {
  EXPECT_EQ(CountHeld(HeldInClass(kBranchImplication, kCIsThree)), "32\n");
  EXPECT_EQ(CountHeld(HeldInline(kBranchImplication, kCIsThree)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kBranchImplication, kCIsThree)), "32\n");
}

TEST(IfElseCases, AForeachInABranchHolds) {
  EXPECT_EQ(CountHeld(HeldInClass(kBranchForeach, kAllTwo)), "32\n");
  EXPECT_EQ(CountHeld(HeldInline(kBranchForeach, kAllTwo)), "32\n");
}

TEST(IfElseCases, DISABLED_AForeachInABranchHoldsInAScopeRandomize) {
  EXPECT_EQ(CountHeld(HeldInScope(kBranchForeach, kAllTwo)), "32\n");
}

TEST(IfElseCases, DISABLED_AUniquenessConstraintInABranchHolds) {
  EXPECT_EQ(CountHeld(HeldInClass(kBranchUnique, kPermutation)), "32\n");
  EXPECT_EQ(CountHeld(HeldInline(kBranchUnique, kPermutation)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kBranchUnique, kPermutation)), "32\n");
}

TEST(IfElseCases, DISABLED_ADistInEachBranchHolds) {
  for (const char* items : {kThenDist, kElseDist}) {
    EXPECT_EQ(CountHeld(HeldInClass(items, kAIsSeven)), "32\n") << items;
    EXPECT_EQ(CountHeld(HeldInline(items, kAIsSeven)), "32\n") << items;
    EXPECT_EQ(CountHeld(HeldInScope(items, kAIsSeven)), "32\n") << items;
  }
}

TEST(IfElseCases, DISABLED_ASoftConstraintInABranchHolds) {
  EXPECT_EQ(CountHeld(HeldInClass(kBranchSoft, kAIsSeven)), "32\n");
  EXPECT_EQ(CountHeld(HeldInline(kBranchSoft, kAIsSeven)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kBranchSoft, kAIsSeven)), "32\n");
}

}  // namespace
