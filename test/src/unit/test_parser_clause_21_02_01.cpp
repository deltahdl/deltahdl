#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DisplayInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg clk;\n"
              "  always @(posedge clk)\n"
              "    $display(\"clock edge at %0t\", $time);\n"
              "endmodule\n"));
}

TEST(SchedulingSemanticsParsing, DisplaySystemCall) {
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

TEST(OperatorAndExpressionParsing, SystemCallEmptyArgs) {
  auto r = Parse(
      "module t;\n"
      "  initial $display(5,,2,,3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, SystemCallLeadingEmptyArg) {
  auto r = Parse(
      "module t;\n"
      "  initial $display(,\"hello\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(IoSystemTaskParsing, DisplayParsesAsSystemCall) {
  auto r = Parse(
      "module t;\n"
      "  initial $display(\"hello\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  auto* item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item->body, nullptr);
}

TEST(IoSystemTaskParsing, DisplayBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"hello\");\n"
              "endmodule\n"));
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
