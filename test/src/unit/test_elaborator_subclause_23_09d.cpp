#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kUnresolved =
    "reference to unresolved identifier 'undeclared'";

void ExpectReportedIn(std::string_view body, std::string_view anchor) {
  ElabFixture f;
  std::string src = "module m;\n  int x;\n  initial begin\n" +
                    std::string(body) + "  end\nendmodule\n";
  ElabOk(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kUnresolved,
                            LineHolding(src, anchor), "23.9"));
}

TEST(ReadPositions, UndeclaredNameInAnIfConditionIsReported) {
  ExpectReportedIn("    if (undeclared) x = 1;\n", "if (undeclared)");
}

TEST(ReadPositions, UndeclaredNameInACaseSelectorIsReported) {
  ExpectReportedIn(
      "    case (undeclared)\n"
      "      0: x = 1;\n"
      "      default: x = 2;\n"
      "    endcase\n",
      "case (undeclared)");
}

TEST(ReadPositions, UndeclaredNameInACaseItemIsReported) {
  ExpectReportedIn(
      "    case (x)\n"
      "      undeclared: x = 1;\n"
      "      default: x = 2;\n"
      "    endcase\n",
      "undeclared: x = 1");
}

TEST(ReadPositions, UndeclaredNameInAWhileConditionIsReported) {
  ExpectReportedIn("    while (undeclared) x = 1;\n", "while (undeclared)");
}

TEST(ReadPositions, UndeclaredNameInAForConditionIsReported) {
  ExpectReportedIn("    for (int i = 0; i < undeclared; i = i + 1) x = 1;\n",
                   "i < undeclared");
}

TEST(ReadPositions, UndeclaredNameInAnRsIfElseConditionIsReported) {
  ExpectReportedIn(
      "    randsequence( main )\n"
      "      main : if (undeclared) a else b;\n"
      "      a : { x = 1; };\n"
      "      b : { x = 2; };\n"
      "    endsequence\n",
      "if (undeclared) a else b");
}

TEST(ReadPositions, UndeclaredNameInAnRsCaseExpressionIsReported) {
  ExpectReportedIn(
      "    randsequence( main )\n"
      "      main : case (undeclared)\n"
      "        0 : a;\n"
      "        default : b;\n"
      "      endcase;\n"
      "      a : { x = 1; };\n"
      "      b : { x = 2; };\n"
      "    endsequence\n",
      "case (undeclared)");
}

TEST(ReadPositions, UndeclaredNameInAUnitFunctionsCodeBlockIfIsReported) {
  ElabFixture f;
  ElabOk(
      "function int F();\n"
      "  int x;\n"
      "  randsequence( main )\n"
      "    main : first;\n"
      "    first : { if (undeclared) x = 10; else x = 5; };\n"
      "  endsequence\n"
      "  return x;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kUnresolved, 5, "23.9"));
}

TEST(ReadPositions, DeclaredNamesInEveryPositionAreClean) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int x, y;\n"
             "  initial begin\n"
             "    if (y) x = 1;\n"
             "    case (y)\n"
             "      x: x = 1;\n"
             "      default: x = 2;\n"
             "    endcase\n"
             "    while (y) y = y - 1;\n"
             "    for (int i = 0; i < y; i = i + 1) x = i;\n"
             "    randsequence( main )\n"
             "      main : if (y) a else b;\n"
             "      a : case (y) 0 : b; default : b; endcase;\n"
             "      b : { x = 2; };\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ReadPositions, APatternBindingInAMatchesConditionIsNotReported) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef union tagged {\n"
             "    struct { bit [3:0] val1, val2; } a;\n"
             "    bit b;\n"
             "  } u_t;\n"
             "  u_t u;\n"
             "  int x;\n"
             "  initial begin\n"
             "    if (u matches tagged a '{.v, 0}) x = 1;\n"
             "    case (u) matches\n"
             "      tagged a '{.p, .q} : x = 2;\n"
             "      default : x = 3;\n"
             "    endcase\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ReadPositions, UndeclaredNameInAReturnStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  function int h();\n"
      "    return nosuch;\n"
      "  endfunction\n"
      "  initial $display(\"%0d\", h());\n"
      "  class k;\n"
      "    function int g(); return other; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'nosuch'", 3,
                            "23.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'other'", 7,
                            "23.9"));
}

TEST(ReadPositions, ReturnOfADeclaredNameIsNotReported) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int mv;\n"
             "  function int f1(int a); return a; endfunction\n"
             "  function int f2(); int l; l = 1; return l; endfunction\n"
             "  function int f3(); return mv; endfunction\n"
             "  class k;\n"
             "    int p;\n"
             "    function int g(); return p; endfunction\n"
             "    function k self(); return this; endfunction\n"
             "  endclass\n"
             "endmodule\n"));
}

TEST(ReadPositions, UndeclaredIdentifierInAnEventControlIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q, a;\n"
      "  always @(posedge nosuch1) q <= 1;\n"
      "  always @(nosuch2) q <= 1;\n"
      "  always @(a or nosuch3) q <= 1;\n"
      "  always @(posedge a iff nosuch4) q <= 1;\n"
      "endmodule\n",
      f);
  const char* message = "reference to unresolved identifier";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 3, "23.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 4, "23.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 5, "23.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 6, "23.9"));
}

TEST(ReadPositions, UndeclaredIdentifierInAClockingEventIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic d;\n"
      "  clocking cb @(posedge nosuch);\n"
      "    input d;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'nosuch'", 3,
                            "23.9"));
}

TEST(ReadPositions, DeclaredNamesInEventControlsAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input logic clk);\n"
      "  logic d, q;\n"
      "  event e;\n"
      "  clocking cb @(posedge clk);\n"
      "    input d;\n"
      "  endclocking\n"
      "  always @(cb) q <= 1;\n"
      "  always @(e) q <= 0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
