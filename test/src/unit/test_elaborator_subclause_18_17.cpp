#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kItemNamesNoProduction =
    "randsequence production item names";
constexpr std::string_view kUnresolvedIdentifier =
    "reference to unresolved identifier";

constexpr std::string_view kTopNameNamesNoProduction =
    "as its top-level production, which is not one of the productions it "
    "declares";

std::string RandsequenceOver(std::string_view top, std::string_view rules) {
  return "module m;\n"
         "  initial begin\n"
         "    randsequence(" +
         std::string(top) + ")\n" + std::string(rules) +
         "    endsequence\n"
         "  end\n"
         "endmodule\n";
}

void ExpectReportedOverRandsequence(std::string_view top,
                                    std::string_view rules,
                                    std::string_view message,
                                    std::string_view anchor) {
  ElabFixture f;
  std::string src = RandsequenceOver(top, rules);
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                            LineHolding(src, anchor), "18.17"));
}

TEST(RandsequenceProductionNames, ItemNamingNoDeclaredProductionIsRejected) {
  ExpectReportedOverRandsequence("main",
                                 "      main : first second;\n"
                                 "      first : { ; };\n",
                                 kItemNamesNoProduction, "main : first second");
}

TEST(RandsequenceProductionNames,
     TopLevelNameDesignatingNoProductionIsRejected) {
  ExpectReportedOverRandsequence("mian", "      main : { ; };\n",
                                 kTopNameNamesNoProduction, "randsequence(");
}

TEST(RandsequenceProductionNames,
     IfBranchNamingNoDeclaredProductionIsRejected) {
  ExpectReportedOverRandsequence("main",
                                 "      main : if (1) missing else other;\n"
                                 "      other : { ; };\n",
                                 kItemNamesNoProduction,
                                 "if (1) missing else other");
}

TEST(RandsequenceProductionNames,
     ElseBranchNamingNoDeclaredProductionIsRejected) {
  ExpectReportedOverRandsequence("main",
                                 "      main : if (1) other else missing;\n"
                                 "      other : { ; };\n",
                                 kItemNamesNoProduction,
                                 "if (1) other else missing");
}

TEST(RandsequenceProductionNames, RepeatNamingNoDeclaredProductionIsRejected) {
  ExpectReportedOverRandsequence("main", "      main : repeat(2) missing;\n",
                                 kItemNamesNoProduction, "repeat(2) missing");
}

TEST(RandsequenceProductionNames, CaseArmNamingNoDeclaredProductionIsRejected) {
  ExpectReportedOverRandsequence(
      "main",
      "      main : case (0) 0: missing; default: other; endcase;\n"
      "      other : { ; };\n",
      kItemNamesNoProduction, "0: missing; default: other");
}

TEST(RandsequenceProductionNames,
     RandJoinNamingNoDeclaredProductionIsRejected) {
  ExpectReportedOverRandsequence("main",
                                 "      main : rand join missing other;\n"
                                 "      other : { ; };\n",
                                 kItemNamesNoProduction,
                                 "rand join missing other");
}

TEST(RandsequenceProductionNames, EveryNameResolvingIsReportedNowhere) {
  ElabFixture f;
  std::string src =
      RandsequenceOver("main",
                       "      main : if (1) yes else no;\n"
                       "      yes : repeat(2) pick;\n"
                       "      no : case (0) 0: pick; default: pick; endcase;\n"
                       "      pick : rand join leaf twig;\n"
                       "      twig : leaf;\n"
                       "      leaf : { ; };\n");
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FindDiag(f, kItemNamesNoProduction), nullptr);
  EXPECT_EQ(FindDiag(f, kTopNameNamesNoProduction), nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RandsequenceProductionNames, ReportStandsOnTheLineOfTheOffendingItem) {
  ElabFixture f;
  std::string src = RandsequenceOver("main",
                                     "      main : first;\n"
                                     "      first : { ; };\n"
                                     "      spare : second;\n");
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kItemNamesNoProduction,
                            LineHolding(src, "spare : second"), "18.17"));
}

TEST(RandsequenceProductionNames, TwoBadNamesAreReportedOnTwoLines) {
  ElabFixture f;
  std::string src = RandsequenceOver("main",
                                     "      main : alpha;\n"
                                     "      alpha : missing_one;\n"
                                     "      spare : missing_two;\n");
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'missing_one'",
                            LineHolding(src, "alpha : missing_one"), "18.17"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'missing_two'",
                            LineHolding(src, "spare : missing_two"), "18.17"));
}

TEST(RandsequenceScope, UndeclaredProductionInAClassMethodIsReported) {
  ElabFixture f;
  std::string src =
      "class C;\n"
      "  task go;\n"
      "    randsequence(main)\n"
      "      main : missing;\n"
      "    endsequence\n"
      "  endtask\n"
      "endclass\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kItemNamesNoProduction,
                            LineHolding(src, "main : missing"), "18.17"));
}

TEST(RandsequenceScope, UndeclaredProductionInAPackageSubroutineIsReported) {
  ElabFixture f;
  std::string src =
      "package p;\n"
      "  task go;\n"
      "    randsequence(main)\n"
      "      main : missing;\n"
      "    endsequence\n"
      "  endtask\n"
      "endpackage\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kItemNamesNoProduction,
                            LineHolding(src, "main : missing"), "18.17"));
}

TEST(RandsequenceScope, UndeclaredProductionInAClassInsideAModuleIsReported) {
  ElabFixture f;
  std::string src =
      "module m;\n"
      "  class C;\n"
      "    task go;\n"
      "      randsequence(main)\n"
      "        main : missing;\n"
      "      endsequence\n"
      "    endtask\n"
      "  endclass\n"
      "endmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kItemNamesNoProduction,
                            LineHolding(src, "main : missing"), "18.17"));
}

std::string RandsequenceReadingInto(std::string_view rules) {
  return "module m;\n"
         "  int r;\n"
         "  initial begin\n"
         "    randsequence(main)\n" +
         std::string(rules) +
         "    endsequence\n"
         "  end\n"
         "endmodule\n";
}

TEST(RandsequenceProductionNames, ReturnValueReadInACodeBlockResolves) {
  ElabFixture f;
  std::string src = RandsequenceReadingInto(
      "      void main : a { r = a; } ;\n"
      "      int a : { return 7; } ;\n");
  ElaborateSrc(src, f);
  EXPECT_EQ(FindDiag(f, kUnresolvedIdentifier), nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RandsequenceProductionNames, FormalArgumentReadInACodeBlockResolves) {
  ElabFixture f;
  std::string src = RandsequenceReadingInto(
      "      void main : compute(9) ;\n"
      "      void compute( int v ) : { r = v; } ;\n");
  ElaborateSrc(src, f);
  EXPECT_EQ(FindDiag(f, kUnresolvedIdentifier), nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RandsequenceProductionNames, VoidProductionNameReadIsUnresolved) {
  ElabFixture f;
  std::string src = RandsequenceReadingInto(
      "      void main : a { r = a; } ;\n"
      "      void a : { ; } ;\n");
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kUnresolvedIdentifier,
                            LineHolding(src, "r = a"), "23.9"));
}

TEST(RandsequenceProductionReturns,
     AReturnWithNoValueInAnIntProductionIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module t;\n"
             "  initial begin\n"
             "    randsequence (main)\n"
             "      main : num { $display(\"%0d\", num); } ;\n"
             "      int num : { return; } ;\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return in production 'num', which returns a "
                            "value, gives no value to return",
                            5, "18.17.7"));
}

TEST(RandsequenceProductionReturns,
     ValueLessReturnsInVoidProductionsElaborate) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial begin\n"
             "    randsequence (main)\n"
             "      main : num a b ;\n"
             "      int num : { return 3; } := 1 { return 4; } ;\n"
             "      void a : { return; } ;\n"
             "      b : { return; } ;\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n"));
}

TEST(RandsequenceProductionReturns,
     AClassHandleReturnedFromAnIntProductionIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C; endclass\n"
             "module t;\n"
             "  initial begin\n"
             "    randsequence (main)\n"
             "      main : num ;\n"
             "      int num : { C c = new; return c; } ;\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in production 'num' is not "
                            "assignment-compatible with the production's "
                            "return type",
                            6, "18.17.7"));
}

TEST(RandsequenceProductionReturns,
     AnIntegerReturnedFromAClassProductionIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C; endclass\n"
             "module t;\n"
             "  initial begin\n"
             "    randsequence (main)\n"
             "      main : mk ;\n"
             "      C mk : { } := 1 {\n"
             "        return 5; } ;\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in production 'mk' is not "
                            "assignment-compatible with the production's "
                            "return type",
                            7, "18.17.7"));
}

TEST(RandsequenceProductionReturns, ReturnsOfTheProductionsTypeElaborate) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "class D extends C; endclass\n"
             "module t;\n"
             "  initial begin\n"
             "    randsequence (main)\n"
             "      main : num(2) mk name ;\n"
             "      int num (int v) : { return v; } ;\n"
             "      C mk : { D d = new; return d; } ;\n"
             "      string name : { string s = \"x\"; return s; } ;\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n"));
}

TEST(RandsequenceProductionReturns,
     AReturnReadsTheVariableANestedBlockDeclaresOverAPort) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module t;\n"
             "  initial begin\n"
             "    randsequence (main)\n"
             "      main : mk(1) ;\n"
             "      C mk (int v) : { begin C v = new; return v; end } ;\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n"));
}

TEST(RandsequenceProductionReturns,
     AnIntANestedBlockDeclaresOverAClassPortIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C; endclass\n"
             "module t;\n"
             "  initial begin\n"
             "    randsequence (main)\n"
             "      main : mk(null) ;\n"
             "      C mk (C v) : { begin int v = 1; return v; end } ;\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in production 'mk' is not "
                            "assignment-compatible with the production's "
                            "return type",
                            6, "18.17.7"));
}

TEST(RandsequenceProductionReturns,
     AReturnReadsTheVariableAForLoopDeclaresOverAPort) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module t;\n"
             "  initial begin\n"
             "    randsequence (main)\n"
             "      main : mk(1) ;\n"
             "      C mk (int v) : { for (C v = null; v != null; ) return v; "
             "return null; } ;\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n"));
}

TEST(RandsequenceProductionReturns,
     AnIntAForLoopDeclaresOverAClassPortIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C; endclass\n"
             "module t;\n"
             "  initial begin\n"
             "    randsequence (main)\n"
             "      main : mk(null) ;\n"
             "      C mk (C v) : { for (int v = 0; v < 2; v++) return v; "
             "return null; } ;\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in production 'mk' is not "
                            "assignment-compatible with the production's "
                            "return type",
                            6, "18.17.7"));
}

TEST(RandsequenceProductionReturns,
     AnIntForeachVariableOverAClassPortIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C; endclass\n"
             "module t;\n"
             "  initial begin\n"
             "    randsequence (main)\n"
             "      main : mk(null) ;\n"
             "      C mk (C v) : { int arr[4]; foreach (arr[v]) return v; "
             "return null; } ;\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in production 'mk' is not "
                            "assignment-compatible with the production's "
                            "return type",
                            6, "18.17.7"));
}

TEST(RandsequenceProductionReturns,
     AForeachVariableOverAnAssociativeDimensionHidesAPort) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module t;\n"
             "  initial begin\n"
             "    randsequence (main)\n"
             "      main : mk(null) ;\n"
             "      int mk (C v) : { int by_key[byte]; foreach (by_key[v]) "
             "return v; return 0; } ;\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n"));
}

TEST(RandsequenceProductionReturns,
     AVariableOfTheBlockAroundTheRandsequenceIsChecked) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C; endclass\n"
             "module t;\n"
             "  initial begin\n"
             "    int k = 1;\n"
             "    randsequence (main)\n"
             "      main : mk ;\n"
             "      C mk : { return k; } ;\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in production 'mk' is not "
                            "assignment-compatible with the production's "
                            "return type",
                            7, "18.17.7"));
}

TEST(RandsequenceProductionReturns, AVariableOfTheModuleIsChecked) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C; endclass\n"
             "module t;\n"
             "  int k;\n"
             "  initial begin\n"
             "    randsequence (main)\n"
             "      main : mk ;\n"
             "      C mk : { return k; } ;\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in production 'mk' is not "
                            "assignment-compatible with the production's "
                            "return type",
                            7, "18.17.7"));
}

TEST(RandsequenceProductionReturns, AFormalOfTheEnclosingTaskIsChecked) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C; endclass\n"
             "module t;\n"
             "  task run(int k);\n"
             "    randsequence (main)\n"
             "      main : mk ;\n"
             "      C mk : { return k; } ;\n"
             "    endsequence\n"
             "  endtask\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in production 'mk' is not "
                            "assignment-compatible with the production's "
                            "return type",
                            6, "18.17.7"));
}

TEST(RandsequenceProductionReturns, APropertyOfTheMethodsClassIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "class H;\n"
      "  int k;\n"
      "  task run();\n"
      "    randsequence (main)\n"
      "      main : mk ;\n"
      "      C mk : { return k; } ;\n"
      "    endsequence\n"
      "  endtask\n"
      "endclass\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in production 'mk' is not "
                            "assignment-compatible with the production's "
                            "return type",
                            7, "18.17.7"));
}

TEST(RandsequenceProductionReturns, AForkDeclarationHidesTheNameAroundIt) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module t;\n"
             "  initial begin\n"
             "    C k;\n"
             "    fork\n"
             "      int k;\n"
             "      randsequence (main)\n"
             "        main : num ;\n"
             "        int num : { return k; } ;\n"
             "      endsequence\n"
             "    join\n"
             "  end\n"
             "endmodule\n"));
}

TEST(RandsequenceProductionReturns,
     AnInnerRandsequenceReadsTheCodeBlockAroundIt) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module t;\n"
             "  initial begin\n"
             "    C k;\n"
             "    randsequence (main)\n"
             "      main : outer ;\n"
             "      outer : { int k;\n"
             "        randsequence (inner)\n"
             "          inner : num ;\n"
             "          int num : { return k; } ;\n"
             "        endsequence } ;\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n"));
}

TEST(RandsequenceProductionReturns,
     AMethodOfAnImplicitVariableIsNoHierarchicalName) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int n;\n"
             "  initial\n"
             "    randsequence (main)\n"
             "      main : op { n = op.len(); } ;\n"
             "      string op : { return \"plusminus\"; } ;\n"
             "    endsequence\n"
             "endmodule\n"));
}

TEST(RandsequenceProductionReturns,
     AVoidProductionsNameHeadsAHierarchicalName) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int n;\n"
      "  initial\n"
      "    randsequence (main)\n"
      "      main : p { n = p.len(); } ;\n"
      "      p : { } ;\n"
      "    endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 'p' resolves to no declaration",
                            5, "23.8"));
}

}  // namespace
