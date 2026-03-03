// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection10, VarDeclAssignmentLogic) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  logic [7:0] data = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  EXPECT_NE(mod->items[0]->init_expr, nullptr);
}

// =============================================================================
// LRM section 10.8 -- Operator assignments (+=, -=, etc.)
// =============================================================================
TEST(ParserSection10, OperatorAssignPlusEq) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    a += 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserSection10, OperatorAssignMinusEq) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    a -= 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection10, OperatorAssignStarEq) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    a *= 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

}  // namespace
