#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection6, DynamicCastTask) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef enum { A, B, C } abc_t;\n"
              "  initial begin\n"
              "    abc_t e;\n"
              "    $cast(e, 1);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, DynamicCastFunction) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef enum { X, Y, Z } xyz_t;\n"
              "  initial begin\n"
              "    xyz_t e;\n"
              "    int ok;\n"
              "    ok = $cast(e, 2);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, DynamicCastCall) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    $cast(d, b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$cast");
}

TEST(ParserSection6, DynamicCastInCondition) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if ($cast(d, b))\n"
      "      $display(\"cast ok\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
}

TEST(ParserSection6, DynamicCastAssignResult) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    int ok;\n"
      "    ok = $cast(d, b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

}
