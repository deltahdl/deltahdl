#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SeveritySystemTaskParsing, FatalNoArgsParses) {
  EXPECT_TRUE(ParseOk("module m; initial $fatal; endmodule\n"));
}

TEST(SeveritySystemTaskParsing, FatalFinishNumber0Parses) {
  EXPECT_TRUE(ParseOk("module m; initial $fatal(0); endmodule\n"));
}

TEST(SeveritySystemTaskParsing, FatalFinishNumber1Parses) {
  EXPECT_TRUE(ParseOk("module m; initial $fatal(1); endmodule\n"));
}

TEST(SeveritySystemTaskParsing, FatalFinishNumber2Parses) {
  EXPECT_TRUE(ParseOk("module m; initial $fatal(2); endmodule\n"));
}

TEST(SeveritySystemTaskParsing, FatalWithFinishAndMessage) {
  EXPECT_TRUE(ParseOk("module m; initial $fatal(1, \"boom\"); endmodule\n"));
}

TEST(SeveritySystemTaskParsing, ErrorNoArgsParses) {
  EXPECT_TRUE(ParseOk("module m; initial $error; endmodule\n"));
}

TEST(SeveritySystemTaskParsing, ErrorWithMessageParses) {
  EXPECT_TRUE(ParseOk("module m; initial $error(\"oops\"); endmodule\n"));
}

// Syntax 20-11: the parenthesized argument portion is optional for $warning,
// so a bare call with no parentheses is a legal statement form.
TEST(SeveritySystemTaskParsing, WarningNoArgsParses) {
  EXPECT_TRUE(ParseOk("module m; initial $warning; endmodule\n"));
}

// Syntax 20-11: likewise $info admits a bare no-argument form.
TEST(SeveritySystemTaskParsing, InfoNoArgsParses) {
  EXPECT_TRUE(ParseOk("module m; initial $info; endmodule\n"));
}

TEST(SeveritySystemTaskParsing, WarningWithMessageParses) {
  EXPECT_TRUE(ParseOk("module m; initial $warning(\"careful\"); endmodule\n"));
}

TEST(SeveritySystemTaskParsing, InfoWithMessageParses) {
  EXPECT_TRUE(ParseOk("module m; initial $info(\"fyi\"); endmodule\n"));
}

TEST(SeveritySystemTaskParsing, ErrorWithFormatArgsParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    $error(\"x = %0d, y = %0d\", x, y);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(SeveritySystemTaskParsing, SeverityTaskInsideCoverPassAction) {
  auto r = Parse(
      "module m;\n"
      "  initial cover(c) $info(\"hit\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
}

}  // namespace
