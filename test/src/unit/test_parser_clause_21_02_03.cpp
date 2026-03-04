#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection21, MonitorOnOff) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $monitoron;\n"
              "    $monitoroff;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection4, Sec4_5_MonitorSystemCall) {
  auto r = Parse(
      "module m;\n"
      "  reg a;\n"
      "  initial begin\n"
      "    $monitor(\"a=%b\", a);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$monitor");
}

TEST(ParserSection21, MonitorBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $monitor(\"a=%b b=%b\", a, b);\n"
              "endmodule\n"));
}

TEST(ParserSection21, MonitorbHexOctal) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $monitorb(a);\n"
              "    $monitorh(a);\n"
              "    $monitoro(a);\n"
              "  end\n"
              "endmodule\n"));
}

}
