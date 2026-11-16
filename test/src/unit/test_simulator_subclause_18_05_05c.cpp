#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

const char* const kVars =
    "  rand bit [3:0] a, b, c;\n"
    "  rand bit [1:0] u[4];\n"
    "  rand real r;\n";
const char* const kScopeVars =
    "  bit [3:0] a, b, c;\n"
    "  bit [1:0] u[4];\n"
    "  real r;\n";

std::string Count(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

std::string InClass(const std::string& items, const std::string& check) {
  return "class C;\n" + std::string(kVars) + "  bit g = 1;\n" +
         "  constraint k { " + items +
         " }\n"
         "endclass\n"
         "module t;\n"
         "  int i, held = 0;\n"
         "  initial begin\n"
         "    static C o = new;\n"
         "    for (i = 0; i < 32; i++)\n"
         "      if (o.randomize() && (" +
         check +
         ")) held++;\n"
         "    $display(\"%0d\", held);\n"
         "  end\n"
         "endmodule\n";
}

std::string OutOfBlock(const std::string& items, const std::string& check) {
  return "class C;\n" + std::string(kVars) + "  bit g = 1;\n" +
         "  constraint k;\n"
         "endclass\n"
         "constraint C::k { " +
         items +
         " }\n"
         "module t;\n"
         "  int i, held = 0;\n"
         "  initial begin\n"
         "    static C o = new;\n"
         "    for (i = 0; i < 32; i++)\n"
         "      if (o.randomize() && (" +
         check +
         ")) held++;\n"
         "    $display(\"%0d\", held);\n"
         "  end\n"
         "endmodule\n";
}

std::string Inline(const std::string& items, const std::string& check) {
  return "class C;\n" + std::string(kVars) + "  bit g = 1;\n" +
         "endclass\n"
         "module t;\n"
         "  int i, held = 0;\n"
         "  initial begin\n"
         "    static C o = new;\n"
         "    for (i = 0; i < 32; i++)\n"
         "      if (o.randomize() with { " +
         items + " } && (" + check +
         ")) held++;\n"
         "    $display(\"%0d\", held);\n"
         "  end\n"
         "endmodule\n";
}

std::string Scope(const std::string& items, const std::string& check) {
  std::string c = check;
  for (std::size_t at = c.find("o."); at != std::string::npos;
       at = c.find("o.", at)) {
    c.erase(at, 2);
  }
  return "module t;\n" + std::string(kScopeVars) +
         "  bit g = 1;\n"
         "  int i, held = 0;\n"
         "  initial begin\n"
         "    for (i = 0; i < 32; i++)\n"
         "      if (std::randomize(a, b, c, u, r) with { " +
         items + " } && (" + c +
         ")) held++;\n"
         "    $display(\"%0d\", held);\n"
         "  end\n"
         "endmodule\n";
}

const char* const kTrue = "a == 9; a == 9 -> b == 5;";
const char* const kTrueHolds = "o.b == 5";
const char* const kContra = "b == 4; a == 9 -> b == 5;";
const char* const kContraHolds = "o.a != 9";
const char* const kRealTrue = "r == 2.5; r > 1.0 -> b == 5;";
const char* const kRealContra =
    "b == 4; r > 1.0 -> b == 5; r inside {[0.0:4.0]};";
const char* const kRealContraHolds = "o.r <= 1.0";

TEST(ImplicationCases, InlineFalseExpressionLeavesTheSetFree) {
  EXPECT_NE(Count(Inline("a == 2; a == 9 -> b == 5;", "o.b != 5")), "0\n");
}

TEST(ImplicationCases, InlineUnsatisfiableSetMakesTheExpressionFalse) {
  EXPECT_EQ(Count(Inline("a == 9 -> { b == 3; b == 4; }", "o.a != 9")), "32\n");
}

TEST(ImplicationCases, ScopeRandomizeTrueDirection) {
  EXPECT_EQ(Count(Scope(kTrue, kTrueHolds)), "32\n");
  EXPECT_EQ(Count(Scope(kRealTrue, kTrueHolds)), "32\n");
}

TEST(ImplicationCases, ScopeRandomizeFalseDirection) {
  EXPECT_NE(Count(Scope("a == 2; a == 9 -> b == 5;", "o.b != 5")), "0\n");
  EXPECT_NE(Count(Scope("r == 0.5; r > 1.0 -> b == 5;", "o.b != 5")), "0\n");
}

TEST(ImplicationCases, ScopeRandomizeContrapositive) {
  EXPECT_EQ(Count(Scope(kContra, kContraHolds)), "32\n");
  EXPECT_EQ(Count(Scope(kRealContra, kRealContraHolds)), "32\n");
}

TEST(ImplicationCases, OutOfBlockEachDirection) {
  EXPECT_EQ(Count(OutOfBlock(kTrue, kTrueHolds)), "32\n");
  EXPECT_NE(Count(OutOfBlock("a == 2; a == 9 -> b == 5;", "o.b != 5")), "0\n");
  EXPECT_EQ(Count(OutOfBlock(kContra, kContraHolds)), "32\n");
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
  EXPECT_EQ(Count(InClass(kInside, kInsideHolds)), "32\n");
  EXPECT_EQ(Count(Inline(kInside, kInsideHolds)), "32\n");
  EXPECT_EQ(Count(Scope(kInside, kInsideHolds)), "32\n");
}

TEST(ImplicationCases, AForeachConsequentHolds) {
  EXPECT_EQ(Count(InClass(kForeach, kForeachHolds)), "32\n");
  EXPECT_EQ(Count(Inline(kForeach, kForeachHolds)), "32\n");
}

TEST(ImplicationCases, DISABLED_AForeachConsequentHoldsInAScopeRandomize) {
  EXPECT_EQ(Count(Scope(kForeach, kForeachHolds)), "32\n");
}

TEST(ImplicationCases, ANestedImplicationHolds) {
  EXPECT_EQ(Count(InClass(kNested, kNestedHolds)), "32\n");
  EXPECT_EQ(Count(Inline(kNested, kNestedHolds)), "32\n");
  EXPECT_EQ(Count(Scope(kNested, kNestedHolds)), "32\n");
}

TEST(ImplicationCases, AnUnparenthesisedChainHolds) {
  EXPECT_EQ(Count(InClass(kChain, kNestedHolds)), "32\n");
  EXPECT_EQ(Count(Inline(kChain, kNestedHolds)), "32\n");
  EXPECT_EQ(Count(Scope(kChain, kNestedHolds)), "32\n");
}

TEST(ImplicationCases, DISABLED_ABracedIfElseConsequentHolds) {
  EXPECT_EQ(Count(InClass(kIfBraced, kIfHolds)), "32\n");
  EXPECT_EQ(Count(Inline(kIfBraced, kIfHolds)), "32\n");
  EXPECT_EQ(Count(Scope(kIfBraced, kIfHolds)), "32\n");
}

TEST(ImplicationCases, DISABLED_AnUnbracedIfElseConsequentHolds) {
  EXPECT_EQ(Count(InClass(kIfBare, kIfHolds)), "32\n");
  EXPECT_EQ(Count(Inline(kIfBare, kIfHolds)), "32\n");
  EXPECT_EQ(Count(Scope(kIfBare, kIfHolds)), "32\n");
}

TEST(ImplicationCases, DISABLED_AUniquenessConsequentHolds) {
  EXPECT_EQ(Count(InClass(kUnique, kUniqueHolds)), "32\n");
  EXPECT_EQ(Count(Inline(kUnique, kUniqueHolds)), "32\n");
  EXPECT_EQ(Count(Scope(kUnique, kUniqueHolds)), "32\n");
}

TEST(ImplicationCases, DISABLED_ADistConsequentHolds) {
  EXPECT_EQ(Count(InClass(kDist, kDistHolds)), "32\n");
  EXPECT_EQ(Count(Inline(kDist, kDistHolds)), "32\n");
  EXPECT_EQ(Count(Scope(kDist, kDistHolds)), "32\n");
}

}  // namespace
