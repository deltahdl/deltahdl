// Tests for the §23.9 scope rules as they reach a read that stands somewhere
// other than an assignment's right side. §23.9 resolves an identifier
// referenced without a hierarchical path against the declarations its scope
// can reach, and §6.5 has data declared before it is used, and neither rule
// says anything about the position the read stands in -- yet the collector of
// reads (CollectProcRhsIdents in
// src/elaborator/elaborator_scope_rules_names.cpp) read an assignment's right
// side and a display task's arguments and nothing else, so `if (undeclared)
// ...` elaborated clean. Every case here puts one read in one position and says
// whether §23.9 reports it.
//
// The cases over a module's assignments are in
// test_elaborator_subclause_23_09a.cpp, those over generate blocks in 23_09b,
// and those over the subroutines no module holds in 23_09c.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kUnresolved =
    "reference to unresolved identifier 'undeclared'";

// Elaborates `body`, the statements of an initial block in a module declaring
// `int x;`, and asserts the §23.9 report stands on the line holding `anchor`.
void ExpectReportedIn(std::string_view body, std::string_view anchor) {
  ElabFixture f;
  std::string src = "module m;\n  int x;\n  initial begin\n" +
                    std::string(body) + "  end\nendmodule\n";
  ElabOk(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kUnresolved,
                            LineHolding(src, anchor), "23.9"));
}

// The condition of an if (Stmt::condition).
TEST(ReadPositions, UndeclaredNameInAnIfConditionIsReported) {
  ExpectReportedIn("    if (undeclared) x = 1;\n", "if (undeclared)");
}

// The selector of a case, held in the same field.
TEST(ReadPositions, UndeclaredNameInACaseSelectorIsReported) {
  ExpectReportedIn(
      "    case (undeclared)\n"
      "      0: x = 1;\n"
      "      default: x = 2;\n"
      "    endcase\n",
      "case (undeclared)");
}

// A case item's pattern, a value the selector is compared with (§12.5).
TEST(ReadPositions, UndeclaredNameInACaseItemIsReported) {
  ExpectReportedIn(
      "    case (x)\n"
      "      undeclared: x = 1;\n"
      "      default: x = 2;\n"
      "    endcase\n",
      "undeclared: x = 1");
}

// The condition of a while loop.
TEST(ReadPositions, UndeclaredNameInAWhileConditionIsReported) {
  ExpectReportedIn("    while (undeclared) x = 1;\n", "while (undeclared)");
}

// The condition of a for loop (Stmt::for_cond), beside the loop's own control
// variable, which §12.7.1 declares and which is not reported.
TEST(ReadPositions, UndeclaredNameInAForConditionIsReported) {
  ExpectReportedIn("    for (int i = 0; i < undeclared; i = i + 1) x = 1;\n",
                   "i < undeclared");
}

// The condition of a randsequence rs_if_else production (§18.17.2), which is
// an expression of the production rather than of any statement.
TEST(ReadPositions, UndeclaredNameInAnRsIfElseConditionIsReported) {
  ExpectReportedIn(
      "    randsequence( main )\n"
      "      main : if (undeclared) a else b;\n"
      "      a : { x = 1; };\n"
      "      b : { x = 2; };\n"
      "    endsequence\n",
      "if (undeclared) a else b");
}

// The case expression of a randsequence rs_case production (§18.17.3).
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

// The shape of sv-tests' 18.17.2--if-else-production-statements_0_fail.sv:
// the read in an if inside a production code block of a compilation-unit
// function, reached through the walk of test_elaborator_subclause_23_09c.cpp
// and the position this file adds. Line 5 is the code block.
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

// The controls. A declared name in each of the positions above resolves, and
// the for loop's control variable resolves in its own condition (§12.7.1).
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

// §12.6: a pattern of the form `. variable_identifier` declares a variable
// rather than reading one, so the `.v` of a matches condition is not a read
// this reports, whatever the case's selector or the if's condition holds.
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

}  // namespace
