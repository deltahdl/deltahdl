// §17.3: Checker instantiation

#include "fixture_checker_elab.h"

namespace {

TEST(CheckerElab, CheckerInstantiatedFromModule) {
  CheckerElabFixture f;
  auto* design = ElaborateSource(
      "checker sub_chk(input logic a);\n"
      "endchecker\n"
      "module top;\n"
      "  logic sig;\n"
      "  sub_chk u0(.a(sig));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_NE(mod->children[0].resolved, nullptr);
  EXPECT_EQ(mod->children[0].resolved->name, "sub_chk");
}

// =============================================================================
// Elaboration tests -- checker instantiation resolved through elaborator
// =============================================================================
// --- Elaborator resolves checker instantiation within a module ---
TEST(ParserAnnexA0414, ElaborationCheckerInstInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "checker my_chk(input logic clk, input logic rst);\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk, rst;\n"
      "  my_chk u0(.clk(clk), .rst(rst));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "my_chk");
  EXPECT_EQ(top->children[0].inst_name, "u0");
  EXPECT_NE(top->children[0].resolved, nullptr);
}

}  // namespace
