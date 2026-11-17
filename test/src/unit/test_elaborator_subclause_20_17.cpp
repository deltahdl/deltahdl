#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SystemCallShape, OneQuotedCommandIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int r;\n"
      "  string c, s;\n"
      "  initial r = $system(\"true\");\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(SystemCallShape, EmptyParenthesesAreAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int r;\n"
      "  string c, s;\n"
      "  initial r = $system();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(SystemCallShape, DISABLED_TwoArgumentsAreReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  int r;\n"
      "  string c, s;\n"
      "  initial r = $system(\"true\", \"x\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$system takes no argument or one quoted command",
                            4, "20.17.1"));
}

TEST(SystemCallShape, DISABLED_NoParenthesesAsAStatementIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  int r;\n"
      "  string c, s;\n"
      "  initial $system;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$system takes no argument or one quoted command",
                            4, "20.17.1"));
}

TEST(SystemCallShape, DISABLED_NoParenthesesAsAnOperandIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  int r;\n"
      "  string c, s;\n"
      "  initial r = $system;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$system takes no argument or one quoted command",
                            4, "20.17.1"));
}

TEST(SystemCallShape, DISABLED_ANumericArgumentIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  int r;\n"
      "  string c, s;\n"
      "  initial r = $system(5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$system takes no argument or one quoted command",
                            4, "20.17.1"));
}

TEST(SystemCallShape, DISABLED_AStringVariableArgumentIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  int r;\n"
      "  string c, s;\n"
      "  initial r = $system(c);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$system takes no argument or one quoted command",
                            4, "20.17.1"));
}

TEST(StacktraceCallShape, TheBareStatementIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int r;\n"
      "  string c, s;\n"
      "  initial $stacktrace;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(StacktraceCallShape, TheBareOperandIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int r;\n"
      "  string c, s;\n"
      "  initial s = $stacktrace;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(StacktraceCallShape, DISABLED_AnArgumentAsAStatementIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  int r;\n"
      "  string c, s;\n"
      "  initial $stacktrace(1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$stacktrace is written without an argument list",
                            4, "20.17.2"));
}

TEST(StacktraceCallShape, DISABLED_AnArgumentAsAnOperandIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  int r;\n"
      "  string c, s;\n"
      "  initial s = $stacktrace(1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$stacktrace is written without an argument list",
                            4, "20.17.2"));
}

TEST(StacktraceCallShape, DISABLED_EmptyParenthesesAsAStatementAreReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  int r;\n"
      "  string c, s;\n"
      "  initial $stacktrace();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$stacktrace is written without an argument list",
                            4, "20.17.2"));
}

TEST(StacktraceCallShape, DISABLED_EmptyParenthesesAsAnOperandAreReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  int r;\n"
      "  string c, s;\n"
      "  initial s = $stacktrace();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$stacktrace is written without an argument list",
                            4, "20.17.2"));
}

}  // namespace
