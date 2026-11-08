#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(EventComparisonElaborator, AllowedComparisonOperatorsAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event a, b;\n"
             "  logic w, x, y, z, t;\n"
             "  initial begin\n"
             "    w = (a == b);\n"
             "    x = (a != b);\n"
             "    y = (a === b);\n"
             "    z = (a !== b);\n"
             "    if (a) t = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(EventComparisonElaborator, ComparisonAgainstNullAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event a;\n"
             "  logic w, x, y, z;\n"
             "  initial begin\n"
             "    w = (a == null);\n"
             "    x = (a != null);\n"
             "    y = (a === null);\n"
             "    z = (a !== null);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(EventComparisonElaborator, RelationalOperatorRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic x;\n"
      "  initial x = (a < b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '<' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

TEST(EventComparisonElaborator, ArithmeticOperatorRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a;\n"
      "  logic [31:0] x;\n"
      "  initial x = a + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

TEST(EventComparisonElaborator, BitwiseOperatorRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic x;\n"
      "  initial x = (a & b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '&' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

TEST(EventComparisonElaborator, UnaryOperatorRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a;\n"
      "  logic [31:0] x;\n"
      "  initial x = ~a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unary operator '~' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

TEST(EventComparisonElaborator, PostfixIncrementOperatorRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a;\n"
      "  logic [31:0] x;\n"
      "  initial x = a++;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "postfix operator '++' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

TEST(EventComparisonElaborator, UnaryOperatorReportNamesTheOperator) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a;\n"
      "  logic [31:0] x;\n"
      "  initial x = -a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unary operator '-' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

TEST(EventComparisonElaborator, OperatorKindsReportDistinguishably) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic [31:0] x, y, z;\n"
      "  initial x = a + b;\n"
      "  initial y = ~a;\n"
      "  initial z = a++;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unary operator '~' is not allowed on event "
                            "variable",
                            5, "15.5.5.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "postfix operator '++' is not allowed on event "
                            "variable",
                            6, "15.5.5.3"));
}

TEST(EventComparisonElaborator, ArithmeticOperatorInForkArmRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic [31:0] x;\n"
      "  initial fork\n"
      "    x = a + b;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            5, "15.5.5.3"));
}

TEST(EventComparisonElaborator, ArithmeticOperatorInForInitializationRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic [31:0] x;\n"
      "  initial for (x = a + b; x < 1; x = x + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

TEST(EventComparisonElaborator, ArithmeticOperatorInForStepRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic [31:0] x;\n"
      "  initial for (x = 0; x < 1; x = a + b) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

TEST(EventComparisonElaborator,
     ArithmeticOperatorInAssertionPassStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic [31:0] x;\n"
      "  initial assert (1) x = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

TEST(EventComparisonElaborator,
     ArithmeticOperatorInAssertionFailStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic [31:0] x;\n"
      "  initial assert (1) else x = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

TEST(EventComparisonElaborator, ArithmeticOperatorInRandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic [31:0] x;\n"
      "  initial randcase\n"
      "    1 : x = a + b;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            5, "15.5.5.3"));
}

TEST(EventComparisonElaborator,
     ArithmeticOperatorInRandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = a + b; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            6, "15.5.5.3"));
}

}  // namespace
