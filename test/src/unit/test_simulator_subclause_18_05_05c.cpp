#include <gtest/gtest.h>

#include "helpers_constraint_places.h"

using namespace delta;

namespace {

const char* const kTrue = "a == 9; a == 9 -> b == 5;";
const char* const kTrueHolds = "o.b == 5";
const char* const kContra = "b == 4; a == 9 -> b == 5;";
const char* const kContraHolds = "o.a != 9";
const char* const kRealTrue = "r == 2.5; r > 1.0 -> b == 5;";
const char* const kRealContra =
    "b == 4; r > 1.0 -> b == 5; r inside {[0.0:4.0]};";
const char* const kRealContraHolds = "o.r <= 1.0";

TEST(ImplicationCases, InlineFalseExpressionLeavesTheSetFree) {
  EXPECT_NE(CountHeld(HeldInline("a == 2; a == 9 -> b == 5;", "o.b != 5")),
            "0\n");
}

TEST(ImplicationCases, InlineUnsatisfiableSetMakesTheExpressionFalse) {
  EXPECT_EQ(CountHeld(HeldInline("a == 9 -> { b == 3; b == 4; }", "o.a != 9")),
            "32\n");
}

TEST(ImplicationCases, ScopeRandomizeTrueDirection) {
  EXPECT_EQ(CountHeld(HeldInScope(kTrue, kTrueHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kRealTrue, kTrueHolds)), "32\n");
}

TEST(ImplicationCases, ScopeRandomizeFalseDirection) {
  EXPECT_NE(CountHeld(HeldInScope("a == 2; a == 9 -> b == 5;", "o.b != 5")),
            "0\n");
  EXPECT_NE(CountHeld(HeldInScope("r == 0.5; r > 1.0 -> b == 5;", "o.b != 5")),
            "0\n");
}

TEST(ImplicationCases, ScopeRandomizeContrapositive) {
  EXPECT_EQ(CountHeld(HeldInScope(kContra, kContraHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kRealContra, kRealContraHolds)), "32\n");
}

TEST(ImplicationCases, OutOfBlockEachDirection) {
  EXPECT_EQ(CountHeld(HeldOutOfBlock(kTrue, kTrueHolds)), "32\n");
  EXPECT_NE(CountHeld(HeldOutOfBlock("a == 2; a == 9 -> b == 5;", "o.b != 5")),
            "0\n");
  EXPECT_EQ(CountHeld(HeldOutOfBlock(kContra, kContraHolds)), "32\n");
}

const char* const kInside = "g -> a inside {3, 5};";
const char* const kInsideHolds = "o.a == 3 || o.a == 5";
const char* const kForeach = "g -> foreach (u[i]) u[i] == 2;";
const char* const kForeachHolds =
    "o.u[0] == 2 && o.u[1] == 2 && o.u[2] == 2 && o.u[3] == 2";
const char* const kNested = "a == 9; b == 1; a >= 8 -> (b < 8 -> c == 3);";
const char* const kChain = "a == 9; b == 1; a >= 8 -> b < 8 -> c == 3;";
const char* const kNestedHolds = "o.c == 3";
const char* const kIfBraced = "g -> { if (a > 7) b == 1; else b == 2; }";
const char* const kIfBare = "g -> if (a > 7) b == 1; else b == 2;";
const char* const kIfHolds = "o.a > 7 ? o.b == 1 : o.b == 2";
const char* const kUnique = "g -> unique {u};";
const char* const kUniqueHolds =
    "o.u[0] != o.u[1] && o.u[0] != o.u[2] && o.u[0] != o.u[3] && o.u[1] != "
    "o.u[2] && o.u[1] != o.u[3] && o.u[2] != o.u[3]";
const char* const kDist = "g -> a dist {7 := 1};";
const char* const kDistHolds = "o.a == 7";

TEST(ImplicationCases, AnInsideConsequentHolds) {
  EXPECT_EQ(CountHeld(HeldInClass(kInside, kInsideHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInline(kInside, kInsideHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kInside, kInsideHolds)), "32\n");
}

TEST(ImplicationCases, AForeachConsequentHolds) {
  EXPECT_EQ(CountHeld(HeldInClass(kForeach, kForeachHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInline(kForeach, kForeachHolds)), "32\n");
}

TEST(ImplicationCases, DISABLED_AForeachConsequentHoldsInAScopeRandomize) {
  EXPECT_EQ(CountHeld(HeldInScope(kForeach, kForeachHolds)), "32\n");
}

TEST(ImplicationCases, ANestedImplicationHolds) {
  EXPECT_EQ(CountHeld(HeldInClass(kNested, kNestedHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInline(kNested, kNestedHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kNested, kNestedHolds)), "32\n");
}

TEST(ImplicationCases, AnUnparenthesisedChainHolds) {
  EXPECT_EQ(CountHeld(HeldInClass(kChain, kNestedHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInline(kChain, kNestedHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kChain, kNestedHolds)), "32\n");
}

TEST(ImplicationCases, DISABLED_ABracedIfElseConsequentHolds) {
  EXPECT_EQ(CountHeld(HeldInClass(kIfBraced, kIfHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInline(kIfBraced, kIfHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kIfBraced, kIfHolds)), "32\n");
}

TEST(ImplicationCases, DISABLED_AnUnbracedIfElseConsequentHolds) {
  EXPECT_EQ(CountHeld(HeldInClass(kIfBare, kIfHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInline(kIfBare, kIfHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kIfBare, kIfHolds)), "32\n");
}

TEST(ImplicationCases, DISABLED_AUniquenessConsequentHolds) {
  EXPECT_EQ(CountHeld(HeldInClass(kUnique, kUniqueHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInline(kUnique, kUniqueHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kUnique, kUniqueHolds)), "32\n");
}

TEST(ImplicationCases, DISABLED_ADistConsequentHolds) {
  EXPECT_EQ(CountHeld(HeldInClass(kDist, kDistHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInline(kDist, kDistHolds)), "32\n");
  EXPECT_EQ(CountHeld(HeldInScope(kDist, kDistHolds)), "32\n");
}

}  // namespace
