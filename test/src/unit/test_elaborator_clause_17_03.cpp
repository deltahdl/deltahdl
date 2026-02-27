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

}  // namespace
