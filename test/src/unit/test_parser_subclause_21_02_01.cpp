#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DisplaySystemCall) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$display");
}

TEST(IoSystemTaskParsing, SystemCallEmptyArgs) {
  auto r = Parse(
      "module t;\n"
      "  initial $display(5,,2,,3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(IoSystemTaskParsing, SystemCallLeadingEmptyArg) {
  auto r = Parse(
      "module t;\n"
      "  initial $display(,\"hello\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Claim 1 (Syntax 21-1): the "( list_of_arguments )" group is optional and the
// list inside it may itself be empty. An empty parenthesized call is a distinct
// surface form from the parenthesis-free call, so the parser must accept it and
// produce a system call carrying no arguments. (Its runtime effect -- a bare
// newline for $display -- is checked in the simulator suite.)
TEST(IoSystemTaskParsing, DisplayEmptyParens) {
  auto r = Parse(
      "module t;\n"
      "  initial $display();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$display");
  EXPECT_TRUE(stmt->expr->args.empty());
}

TEST(IoSystemTaskParsing, DisplayNoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display;\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DisplayMultipleArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"x=%d y=%h\", x, y);\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, WriteBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $write(\"no newline\");\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, WriteNoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $write;\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DisplaybHexOctal) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $displayb(\"binary: \", val);\n"
              "    $displayh(\"hex: \", val);\n"
              "    $displayo(\"octal: \", val);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, WritebHexOctal) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $writeb(val);\n"
              "    $writeh(val);\n"
              "    $writeo(val);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
