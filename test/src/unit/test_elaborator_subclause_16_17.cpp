#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(ExpectStatementElaboration, ATaskExpectTakesTheDefaultClocking) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic clk;\n"
      "  int data;\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "  property within_ten(int value);\n"
      "    ##[1:10] data == value;\n"
      "  endproperty\n"
      "  task automatic wait_for(integer value, output bit success);\n"
      "    expect (within_ten(value)) success = 1;\n"
      "      else success = 0;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->function_decls.size(), 1u);
  ASSERT_EQ(mod->function_decls[0]->func_body_stmts.size(), 1u);
  const Stmt* expect = mod->function_decls[0]->func_body_stmts[0];
  EXPECT_EQ(expect->kind, StmtKind::kExpect);
  EXPECT_TRUE(expect->is_concurrent_clocked);
  ASSERT_EQ(expect->assert_clock.size(), 1u);
  EXPECT_EQ(expect->assert_clock[0].edge, Edge::kPosedge);
}

}  // namespace
