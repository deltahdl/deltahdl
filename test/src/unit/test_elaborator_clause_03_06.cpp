#include "fixture_elaborator.h"

namespace {

TEST(DesignBuildingBlockElaboration, CheckerWithModelingCodeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      "  logic flag;\n"
      "  initial flag = 0;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DesignBuildingBlockElaboration, CheckerWithPortsElaborates) {
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

TEST(CheckerDefinitions, EmptyCheckerElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc("checker chk; endchecker\n", f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
