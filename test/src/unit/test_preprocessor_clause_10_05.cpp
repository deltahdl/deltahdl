#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(AssignmentParsing, VarDeclAssignment) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  int x = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  auto* item = mod->items[0];
  EXPECT_EQ(item->name, "x");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(AssignmentParsing, VarDeclAssignmentLogic) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  logic [7:0] data = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  EXPECT_NE(mod->items[0]->init_expr, nullptr);
}

TEST(VarDeclAssignmentPreprocessor, BlockVarDeclWithInit) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    int x = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* blk = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_GE(blk->stmts.size(), 1u);
  EXPECT_EQ(blk->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_NE(blk->stmts[0]->var_init, nullptr);
}

TEST(VarDeclAssignmentPreprocessor, MixedInitInOneStmt) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  int a = 1, b, c = 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 3u);
  EXPECT_NE(items[0]->init_expr, nullptr);
  EXPECT_EQ(items[1]->init_expr, nullptr);
  EXPECT_NE(items[2]->init_expr, nullptr);
}

}  // namespace
