#include "fixture_checker_elab.h"

namespace {

TEST(CheckerElab, ElaborateCheckerWithPorts) {
  CheckerElabFixture f;
  auto* design = ElaborateSource(
      "checker chk_ports(input logic clk, input logic rst);\n"
      "endchecker\n",
      f, "chk_ports");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].name, "clk");
  EXPECT_EQ(mod->ports[1].name, "rst");
}

TEST(CheckerDeclaration, WithInputPorts) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic clk, input logic rst);\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_GE(design->top_modules[0]->ports.size(), 2u);
}

}  // namespace
