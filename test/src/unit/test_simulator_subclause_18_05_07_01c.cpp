#include <gtest/gtest.h>

#include <string>

#include "helpers_constraint_places.h"

using namespace delta;

namespace {

const char* const kAll = "16\n";

const char* const kAscending =
    "  function bit ok();\n"
    "    if (q.size() < 1 || q.size() > 5) return 0;\n"
    "    foreach (q[k]) if (k > 0 && q[k] <= q[k - 1]) return 0;\n"
    "    return 1;\n"
    "  endfunction\n";
const char* const kSizeAndSort =
    "q.size inside {[1:5]}; foreach (q[k]) (k < q.size - 1) -> q[k + 1] > "
    "q[k];";

TEST(ForeachConstraintCases, AQueueIsSizedBeforeItIsIterated) {
  EXPECT_EQ(Held(std::string("  rand bit [7:0] q[$];\n"
                             "  constraint c { ") +
                     kSizeAndSort + " }\n" + kAscending,
                 "o.ok()"),
            kAll);
}

TEST(ForeachConstraintCases, AnInlineBlockSizesBeforeIterating) {
  EXPECT_EQ(HeldWith(std::string("  rand bit [7:0] q[];\n") + kAscending,
                     kSizeAndSort, "o.ok()"),
            kAll);
}

TEST(ForeachConstraintCases, AnOutOfBlockConstraintSizesBeforeIterating) {
  EXPECT_EQ(
      CountHeld(Tally(
          "",
          std::string("  rand bit [7:0] q[];\n  constraint c;\n") + kAscending,
          std::string("constraint C::c { ") + kSizeAndSort + " }\n",
          "o.randomize()", "o.ok()")),
      kAll);
}

TEST(ForeachConstraintCases, TheSizeAsAStateVariableCanMakeTheSolveFail) {
  EXPECT_EQ(Fails("  rand bit [7:0] q[];\n"
                  "  constraint c1 { q.size inside {[1:2]}; }\n"
                  "  constraint c2 { foreach (q[i]) q.size == 4; }\n"),
            kAll);
}

TEST(ForeachConstraintCases, AnUnguardedIndexPastAFixedArrayIsKept) {
  EXPECT_EQ(Fails("  rand bit [3:0] a[4];\n"
                  "  constraint c { foreach (a[i]) a[i] < a[i + 1]; }\n"),
            kAll);
}

TEST(ForeachConstraintCases, DISABLED_AnUnguardedIndexPastADynamicArrayIsKept) {
  EXPECT_EQ(Fails("  rand bit [3:0] a[];\n"
                  "  constraint s { a.size == 3; }\n"
                  "  constraint c { foreach (a[i]) a[i] < a[i + 1]; }\n"),
            kAll);
}

TEST(ForeachConstraintCases, DISABLED_AnUnguardedIndexPastAQueueIsKept) {
  EXPECT_EQ(Fails("  rand bit [3:0] a[$];\n"
                  "  constraint s { a.size == 3; }\n"
                  "  constraint c { foreach (a[i]) a[i] < a[i + 1]; }\n"),
            kAll);
}

TEST(ForeachConstraintCases, AnUnguardedNegativeIndexIsKept) {
  EXPECT_EQ(Fails("  rand bit [3:0] a[4];\n"
                  "  constraint c { foreach (a[i]) a[i - 1] > a[i]; }\n"),
            kAll);
}

const char* const kThree = "  rand bit [3:0] a[3];\n";
const char* const kThreeDynamic =
    "  rand bit [3:0] a[];\n"
    "  constraint s { a.size == 3; }\n";
const char* const kThreeQueue =
    "  rand bit [3:0] a[$];\n"
    "  constraint s { a.size == 3; }\n";

std::string Body(const char* decls, const std::string& items) {
  return std::string(decls) + "  constraint c { " + items + " }\n";
}

const char* const kGuardedRise = "foreach (a[i]) (i < 2) -> a[i] < a[i + 1];";
const char* const kRises = "o.a[0] < o.a[1] && o.a[1] < o.a[2]";

std::string HeldTwice(const std::string& body, const std::string& check) {
  std::string src = Tally("", body, "", "o.randomize()", check);
  src.replace(src.find("n < 16"), 6, "n < 2");
  return CountHeld(src);
}

TEST(ForeachConstraintCases, AGuardedIndexPastTheEndIsNotCreated) {
  EXPECT_EQ(Held(Body(kThree, kGuardedRise), kRises), kAll);
  EXPECT_EQ(HeldTwice(Body(kThreeDynamic, kGuardedRise), kRises), "2\n");
  EXPECT_EQ(HeldTwice(Body(kThreeQueue, kGuardedRise), kRises), "2\n");
}

const char* const kHandleGuard =
    "  rand bit [3:0] a[3];\n"
    "  D h[3];\n"
    "  constraint c { foreach (a[i]) (h[i] != null) -> a[i] == 5; }\n"
    "  function new(); h[1] = new; endfunction\n";

TEST(ForeachConstraintCases, AHandleComparisonGuardsTheConstraint) {
  EXPECT_EQ(CountHeld(Tally("class D; endclass\n", kHandleGuard, "",
                            "o.randomize()", "o.a[1] == 5")),
            kAll);
  EXPECT_NE(CountHeld(Tally("class D; endclass\n", kHandleGuard, "",
                            "o.randomize()", "o.a[0] != 5")),
            "0\n");
}

TEST(ForeachConstraintCases, AGuardOfConstantsAloneSkipsAnOutOfBoundsElement) {
  EXPECT_EQ(Held("  rand bit [3:0] a[4];\n"
                 "  constraint c { foreach (a[i]) (1 == 0) -> a[i + 5] == 1; "
                 "a[0] == 3; }\n",
                 "o.a[0] == 3"),
            kAll);
}

TEST(ForeachConstraintCases, AGuardInAnInlineBlockSkipsTheLastElement) {
  EXPECT_EQ(HeldWith("  rand bit [3:0] a[3];\n", kGuardedRise, kRises), kAll);
}

TEST(ForeachConstraintCases, DISABLED_AGuardInAScopeRandomizeSkipsAnElement) {
  EXPECT_EQ(HeldInScopeOf("  bit [1:0] ban[4] = '{0, 1, 2, 3};\n"
                          "  bit [1:0] x;\n",
                          "std::randomize(x) with { foreach (ban[i]) (i < 3) "
                          "-> x != ban[i]; }",
                          "x == 3"),
            kAll);
}

TEST(ForeachConstraintCases, APredicateOverARandomVariableIsARelation) {
  EXPECT_EQ(Held("  rand bit [3:0] a[4];\n"
                 "  rand bit s;\n"
                 "  constraint c { foreach (a[i]) (s == 1) -> a[i] == 2; "
                 "a[0] == 5; }\n",
                 "o.s == 0"),
            kAll);
}

TEST(ForeachConstraintCases, ALeadingEmptySlotIteratesTheSecondDimension) {
  const char* body = "  rand bit [3:0] m[2][3];\n";
  const char* items = "foreach (m[, j]) m[0][j] == j + 1;";
  const char* check = "o.m[0][0] == 1 && o.m[0][1] == 2 && o.m[0][2] == 3";
  EXPECT_EQ(
      Held(std::string(body) + "  constraint c { " + items + " }\n", check),
      kAll);
  EXPECT_EQ(HeldWith(body, items, check), kAll);
}

TEST(ForeachConstraintCases,
     DISABLED_OneVariableOverTwoDimensionsIteratesTheFirst) {
  const char* body = "  rand bit [3:0] m[3][4];\n";
  const char* items = "foreach (m[j]) m[j][0] == j + 1;";
  const char* check = "o.m[0][0] == 1 && o.m[1][0] == 2 && o.m[2][0] == 3";
  EXPECT_EQ(
      Held(std::string(body) + "  constraint c { " + items + " }\n", check),
      kAll);
  EXPECT_EQ(HeldWith(body, items, check), kAll);
}

TEST(ForeachConstraintCases, AnInteriorEmptySlotSkipsTheMiddleDimension) {
  const char* body = "  rand bit [3:0] m[2][2][3];\n";
  const char* items = "foreach (m[i, , k]) m[i][1][k] == i + k + 1;";
  const char* check =
      "o.m[0][1][0] == 1 && o.m[1][1][2] == 4 && o.m[1][1][0] == 2";
  EXPECT_EQ(
      Held(std::string(body) + "  constraint c { " + items + " }\n", check),
      kAll);
  EXPECT_EQ(HeldWith(body, items, check), kAll);
}

TEST(ForeachConstraintCases, ALoopVariableOverAFixedDimensionIsASignedInt) {
  EXPECT_EQ(Held("  rand int a[2];\n"
                 "  constraint c { foreach (a[k]) a[k] == (k - 1 < 0); }\n",
                 "o.a[0] == 1 && o.a[1] == 0"),
            kAll);
}

TEST(ForeachConstraintCases, ALoopVariableOverADynamicOrQueueIsASignedInt) {
  EXPECT_EQ(Held("  rand int d[], q[$];\n"
                 "  constraint s { d.size == 2; q.size == 2; }\n"
                 "  constraint c { foreach (d[k]) d[k] == (k - 1 < 0); "
                 "foreach (q[k]) q[k] == (k - 1 < 0); }\n",
                 "o.d[0] == 1 && o.d[1] == 0 && o.q[0] == 1 && o.q[1] == 0"),
            kAll);
}

std::string Keyed(const std::string& index, const std::string& keys,
                  const std::string& relation) {
  return "  rand int a[" + index +
         "];\n"
         "  constraint c { foreach (a[k]) a[k] == " +
         relation +
         "; }\n"
         "  function new(); " +
         keys + " endfunction\n";
}

TEST(ForeachConstraintCases, AStringIndexGivesAStringLoopVariable) {
  EXPECT_EQ(Held(Keyed("string", "a[\"x\"] = 0; a[\"y\"] = 0;", "(k == \"x\")"),
                 "o.a[\"x\"] == 1 && o.a[\"y\"] == 0"),
            kAll);
}

TEST(ForeachConstraintCases,
     DISABLED_ASignedByteIndexGivesASignedLoopVariable) {
  EXPECT_EQ(Held(Keyed("byte", "a[-3] = 0; a[5] = 0;", "k"),
                 "o.a[-3] == -3 && o.a[5] == 5"),
            kAll);
}

TEST(ForeachConstraintCases, DISABLED_AnIntIndexGivesAnIntLoopVariable) {
  EXPECT_EQ(Held(Keyed("int", "a[-3] = 0; a[5] = 0;", "k"),
                 "o.a[-3] == -3 && o.a[5] == 5"),
            kAll);
}

TEST(ForeachConstraintCases,
     DISABLED_AnUnsignedIndexGivesAnUnsignedLoopVariable) {
  EXPECT_EQ(Held(Keyed("bit [3:0]", "a[0] = 9; a[2] = 9;", "(k - 1 < 0)"),
                 "o.a[0] == 0 && o.a[2] == 0"),
            kAll);
}

TEST(ForeachConstraintCases, ALoopVariableHidesACallingScopeVariable) {
  EXPECT_EQ(CountHeld("class C;\n"
                      "  rand bit [3:0] a[3];\n"
                      "endclass\n"
                      "module t;\n"
                      "  int i = 7;\n"
                      "  int n, held = 0;\n"
                      "  initial begin\n"
                      "    static C o = new;\n"
                      "    for (n = 0; n < 16; n++)\n"
                      "      if (o.randomize() with { foreach (a[i]) a[i] == "
                      "i; } && o.a[0] == 0 && o.a[2] == 2) held++;\n"
                      "    $display(\"%0d\", held);\n"
                      "  end\n"
                      "endmodule\n"),
            kAll);
}

TEST(ForeachConstraintCases,
     DISABLED_ALoopVariableHidesACallingScopeVariableInAScopeRandomize) {
  EXPECT_EQ(HeldInScopeOf("  int i = 7;\n"
                          "  bit [1:0] st[3];\n"
                          "  bit [1:0] x;\n",
                          "std::randomize(x) with { foreach (st[i]) x != i; }",
                          "x == 3"),
            kAll);
}

TEST(ForeachConstraintCases, SiblingForeachConstraintsReuseALoopVariableName) {
  EXPECT_EQ(Held("  rand bit [3:0] a[3], b[3];\n"
                 "  constraint c { foreach (a[i]) a[i] == i; foreach (b[i]) "
                 "b[i] == i + 1; }\n",
                 "o.a[2] == 2 && o.b[0] == 1 && o.b[2] == 3"),
            kAll);
}

TEST(ForeachConstraintCases, DISABLED_AnIfOnTheLoopVariableHolds) {
  for (const char* decls : {kThree, kThreeDynamic, kThreeQueue}) {
    EXPECT_EQ(Held(Body(decls, "foreach (a[i]) if (i == 1) a[i] == 7;"),
                   "o.a[1] == 7"),
              kAll)
        << decls;
  }
}

TEST(ForeachConstraintCases, DISABLED_AnIfElseInTheBodyHolds) {
  EXPECT_EQ(Held(Body(kThree,
                      "foreach (a[i]) if (i == 0) a[i] == 3; else a[i] == 4;"),
                 "o.a[0] == 3 && o.a[1] == 4 && o.a[2] == 4"),
            kAll);
}

TEST(ForeachConstraintCases, DISABLED_AnIfOnAStateOrRandomVariableHolds) {
  EXPECT_EQ(Held(Body("  rand bit [3:0] a[3];\n  bit g = 1;\n",
                      "foreach (a[i]) if (g) a[i] == 6;"),
                 "o.a[0] == 6 && o.a[2] == 6"),
            kAll);
  EXPECT_EQ(Held(Body("  rand bit [3:0] a[3];\n  rand bit s;\n",
                      "s == 1; foreach (a[i]) if (s) a[i] == 6;"),
                 "o.a[0] == 6 && o.a[2] == 6"),
            kAll);
}

TEST(ForeachConstraintCases, DISABLED_AnIfRelatingNeighboursHolds) {
  EXPECT_EQ(Held(Body(kThree,
                      "a[0] == 2; foreach (a[i]) if (i > 0) a[i] == a[i - 1] "
                      "+ 1;"),
                 "o.a[0] == 2 && o.a[1] == 3 && o.a[2] == 4"),
            kAll);
}

TEST(ForeachConstraintCases, DISABLED_AnIfInAnInlineForeachHolds) {
  EXPECT_EQ(
      HeldWith(kThree, "foreach (a[i]) if (i == 1) a[i] == 7;", "o.a[1] == 7"),
      kAll);
}

TEST(ForeachConstraintCases, DISABLED_ADistInTheBodyHolds) {
  EXPECT_EQ(Held(Body(kThree, "foreach (a[i]) a[i] dist {9 := 1};"),
                 "o.a[0] == 9 && o.a[1] == 9 && o.a[2] == 9"),
            kAll);
}

TEST(ForeachConstraintCases, DISABLED_ASoftConstraintInTheBodyHolds) {
  EXPECT_EQ(Held(Body(kThree, "foreach (a[i]) soft a[i] == 9;"),
                 "o.a[0] == 9 && o.a[1] == 9 && o.a[2] == 9"),
            kAll);
}

TEST(ForeachConstraintCases, DISABLED_AUniquenessConstraintOverARowHolds) {
  EXPECT_EQ(Held(Body("  rand bit [1:0] m[2][4];\n"
                      "  function bit ok();\n"
                      "    foreach (m[i, j]) foreach (m[, k])\n"
                      "      if (j != k && m[i][j] == m[i][k]) return 0;\n"
                      "    return 1;\n"
                      "  endfunction\n",
                      "foreach (m[i]) unique {m[i]};"),
                 "o.ok()"),
            kAll);
}

const char* const kGrid = "  rand bit [3:0] m[2][3];\n";
const char* const kGridHolds =
    "o.m[0][0] == 0 && o.m[0][2] == 2 && o.m[1][0] == 1 && o.m[1][2] == 3";

TEST(ForeachConstraintCases, DISABLED_AForeachNestedInTheBodyHolds) {
  EXPECT_EQ(
      Held(Body(kGrid, "foreach (m[i]) foreach (m[, j]) m[i][j] == i + j;"),
           kGridHolds),
      kAll);
  EXPECT_EQ(
      Held(Body(kGrid, "foreach (m[i]) { foreach (m[, j]) m[i][j] == i + j; }"),
           kGridHolds),
      kAll);
}

TEST(ForeachConstraintCases, ABracedSetOfRelationsInTheBodyHolds) {
  EXPECT_EQ(Held(Body(kThree, "foreach (a[i]) { a[i] > 2; a[i] < 4; }"),
                 "o.a[0] == 3 && o.a[1] == 3 && o.a[2] == 3"),
            kAll);
}

TEST(ForeachConstraintCases, DISABLED_AStringIsIteratedInAScopeRandomize) {
  EXPECT_EQ(HeldInScopeOf("  string s = \"abc\";\n"
                          "  bit [7:0] x;\n",
                          "std::randomize(x) with { foreach (s[i]) x != s[i]; "
                          "x inside {[97:100]}; }",
                          "x == 100"),
            kAll);
}

TEST(ForeachConstraintCases, AStringIsIteratedOutOfBlock) {
  EXPECT_EQ(CountHeld(Tally("",
                            "  string s = \"abc\";\n"
                            "  rand bit [7:0] x;\n"
                            "  constraint k;\n",
                            "constraint C::k { foreach (s[i]) x != s[i]; x "
                            "inside {[97:100]}; }\n",
                            "o.randomize()", "o.x == 100")),
            kAll);
}

TEST(ForeachConstraintCases, AnEmptyStringImposesNothing) {
  EXPECT_EQ(
      Held("  string s = \"\";\n"
           "  rand bit [7:0] x;\n"
           "  constraint k { foreach (s[i]) x == 0; x inside {[5:6]}; }\n",
           "o.x == 5 || o.x == 6"),
      kAll);
}

TEST(ForeachConstraintCases, AQueueIsIterated) {
  EXPECT_EQ(Held(Body(kThreeQueue, "foreach (a[i]) a[i] == i + 1;"),
                 "o.a[0] == 1 && o.a[2] == 3"),
            kAll);
}

TEST(ForeachConstraintCases, AnAssociativeArrayIsIterated) {
  EXPECT_EQ(Held(Keyed("int", "a[2] = 0; a[7] = 0;", "k + 1"),
                 "o.a[2] == 3 && o.a[7] == 8"),
            kAll);
  EXPECT_EQ(Held(Keyed("string", "a[\"p\"] = 0; a[\"q\"] = 0;",
                       "(k == \"p\" ? 4 : 9)"),
                 "o.a[\"p\"] == 4 && o.a[\"q\"] == 9"),
            kAll);
}

TEST(ForeachConstraintCases, DISABLED_APackedVectorIsIterated) {
  EXPECT_EQ(Held("  rand bit [3:0] v;\n"
                 "  constraint c { foreach (v[i]) v[i] == (i % 2); }\n",
                 "o.v == 4'b1010"),
            kAll);
}

TEST(ForeachConstraintCases, DISABLED_APackedTwoDimensionalArrayIsIterated) {
  EXPECT_EQ(Held("  rand bit [1:0][2:0] p;\n"
                 "  constraint c { foreach (p[i, j]) p[i][j] == (i == j); }\n",
                 "o.p[0][0] == 1 && o.p[1][1] == 1 && o.p[0][1] == 0 && "
                 "o.p[1][2] == 0"),
            kAll);
}

const char* const kNestedSum = "foreach (d[i, j]) d[i][j] == i + j + 1;";
const char* const kNestedSumHolds =
    "o.d[0][1] == 2 && o.d[1][0] == 2 && o.d[1].size() == 2";

TEST(ForeachConstraintCases, DISABLED_ADynamicArrayOfDynamicArraysIsIterated) {
  EXPECT_EQ(Held(Body("  rand bit [3:0] d[][];\n"
                      "  function new(); d = new[2]; d[0] = new[2]; "
                      "d[1] = new[2]; endfunction\n",
                      kNestedSum),
                 kNestedSumHolds),
            kAll);
}

TEST(ForeachConstraintCases, DISABLED_AFixedArrayOfDynamicArraysIsIterated) {
  EXPECT_EQ(Held(Body("  rand bit [3:0] d[2][];\n"
                      "  function new(); d[0] = new[2]; d[1] = new[2]; "
                      "endfunction\n",
                      kNestedSum),
                 kNestedSumHolds),
            kAll);
}

TEST(ForeachConstraintCases, DISABLED_AQueueOfFixedArraysIsIterated) {
  EXPECT_EQ(Held(Body("  rand bit [3:0] d[$][2];\n"
                      "  function new(); d.push_back('{0, 0}); "
                      "d.push_back('{0, 0}); endfunction\n",
                      kNestedSum),
                 "o.d[0][1] == 2 && o.d[1][0] == 2 && o.d[1][1] == 3"),
            kAll);
}

TEST(ForeachConstraintCases, DISABLED_AStateArrayIsIteratedInAScopeRandomize) {
  EXPECT_EQ(HeldInScopeOf("  bit [1:0] ban[3] = '{1, 2, 3};\n"
                          "  bit [1:0] x;\n",
                          "std::randomize(x) with { foreach (ban[i]) x != "
                          "ban[i]; }",
                          "x == 0"),
            kAll);
}

TEST(ForeachConstraintCases,
     DISABLED_TheRandomizedArrayIsIteratedInAScopeRandomize) {
  EXPECT_EQ(HeldInScopeOf("  bit [3:0] arr[4];\n",
                          "std::randomize(arr) with { foreach (arr[i]) arr[i] "
                          "== i * 2; }",
                          "arr[1] == 2 && arr[3] == 6"),
            kAll);
}

TEST(ForeachConstraintCases, ADescendingRangeMapsEachIndexToItself) {
  EXPECT_EQ(Held("  rand int a[3:1];\n"
                 "  constraint c { foreach (a[k]) a[k] == k; }\n",
                 "o.a[3] == 3 && o.a[2] == 2 && o.a[1] == 1"),
            kAll);
}

TEST(ForeachConstraintCases, ARangeNotStartingAtZeroMapsEachIndexToItself) {
  EXPECT_EQ(Held("  rand int a[1:3];\n"
                 "  constraint c { foreach (a[k]) a[k] == 10 + k; }\n",
                 "o.a[1] == 11 && o.a[3] == 13"),
            kAll);
}

TEST(ForeachConstraintCases, DISABLED_PackedAndUnpackedDimensionsMapInOrder) {
  EXPECT_EQ(Held("  rand bit [3:0][2:1] B [5:1][4];\n"
                 "  constraint c { foreach (B[q, r, , s]) { B[q][r][3][s] == "
                 "(s == 2); B[q][r][2][s] == (q == 5); B[q][r][1][s] == "
                 "(r == 3); } }\n",
                 "o.B[5][3][3][2] == 1 && o.B[5][3][2][2] == 1 && "
                 "o.B[5][3][1][2] == 1 && o.B[1][0][3][1] == 0 && "
                 "o.B[1][0][2][1] == 0 && o.B[1][0][1][1] == 0"),
            kAll);
}

TEST(ForeachConstraintCases, TheSecondVariableMapsToTheSecondDimension) {
  EXPECT_EQ(
      Held("  rand int m[2][3];\n"
           "  constraint c { foreach (m[i, j]) m[i][j] == 10 * i + j; }\n",
           "o.m[1][2] == 12 && o.m[0][2] == 2 && o.m[1][0] == 10"),
      kAll);
}

}  // namespace
