#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §20.10 Syntax 20-11:
//   severity_system_task ::= $fatal [ ( finish_number [, list_of_arguments ] ) ] ;
//                          | $error   [ ( [ list_of_arguments ] ) ] ;
//                          | $warning [ ( [ list_of_arguments ] ) ] ;
//                          | $info    [ ( [ list_of_arguments ] ) ] ;
//   finish_number ::= 0 | 1 | 2
//
// The four severity system tasks are surfaced as procedural system-call
// statements at parse time. §16.3 cross-links the same tasks into immediate
// assertion action_blocks, so the parser tests below exercise both the
// standalone procedural form and the §16.3 weave point.

TEST(SeveritySystemTaskParsing, FatalNoArgsParses) {
  EXPECT_TRUE(
      ParseOk("module m; initial $fatal; endmodule\n"));
}

TEST(SeveritySystemTaskParsing, FatalFinishNumber0Parses) {
  EXPECT_TRUE(
      ParseOk("module m; initial $fatal(0); endmodule\n"));
}

TEST(SeveritySystemTaskParsing, FatalFinishNumber1Parses) {
  EXPECT_TRUE(
      ParseOk("module m; initial $fatal(1); endmodule\n"));
}

TEST(SeveritySystemTaskParsing, FatalFinishNumber2Parses) {
  EXPECT_TRUE(
      ParseOk("module m; initial $fatal(2); endmodule\n"));
}

TEST(SeveritySystemTaskParsing, FatalWithFinishAndMessage) {
  EXPECT_TRUE(
      ParseOk("module m; initial $fatal(1, \"boom\"); endmodule\n"));
}

TEST(SeveritySystemTaskParsing, ErrorNoArgsParses) {
  EXPECT_TRUE(
      ParseOk("module m; initial $error; endmodule\n"));
}

TEST(SeveritySystemTaskParsing, ErrorWithMessageParses) {
  EXPECT_TRUE(
      ParseOk("module m; initial $error(\"oops\"); endmodule\n"));
}

TEST(SeveritySystemTaskParsing, WarningWithMessageParses) {
  EXPECT_TRUE(
      ParseOk("module m; initial $warning(\"careful\"); endmodule\n"));
}

TEST(SeveritySystemTaskParsing, InfoWithMessageParses) {
  EXPECT_TRUE(
      ParseOk("module m; initial $info(\"fyi\"); endmodule\n"));
}

// §20.10 "user-defined message shall use the same syntax as the $display
// system task and thus can include any number of arguments."
TEST(SeveritySystemTaskParsing, ErrorWithFormatArgsParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    $error(\"x = %0d, y = %0d\", x, y);\n"
              "  end\n"
              "endmodule\n"));
}

// §20.10 also calls out expect and wait_order — they too contain
// action_blocks that may default to $error. We only verify the BNF placement
// of severity tasks inside the action_block here.
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
