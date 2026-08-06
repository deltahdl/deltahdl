#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

TEST_F(ProgramTestParse, ProgramWithExitCall) {
  auto* unit = Parse(
      "program p;\n"
      "  initial begin\n"
      "    $exit;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST_F(ProgramTestParse, ProgramWithExitCallWithParens) {
  auto* unit = Parse(
      "program p;\n"
      "  initial $exit();\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  auto* initial = unit->programs[0]->items[0];
  EXPECT_EQ(initial->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(initial->body, nullptr);
  auto* stmt = initial->body;
  if (stmt->kind == StmtKind::kBlock) {
    ASSERT_EQ(stmt->stmts.size(), 1u);
    stmt = stmt->stmts[0];
  }
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$exit");
  EXPECT_TRUE(stmt->expr->args.empty());
}

TEST_F(ProgramTestParse, ExitOutsideProgramParses) {
  auto* unit = Parse(
      "module m;\n"
      "  initial $exit();\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  ASSERT_EQ(unit->modules.size(), 1u);
  ASSERT_FALSE(unit->modules[0]->items.empty());
  EXPECT_EQ(unit->modules[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}

}  // namespace
