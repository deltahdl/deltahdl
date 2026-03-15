// §25.4

#include "fixture_elaborator.h"

namespace {

TEST(InterfacePorts, InterfaceWithPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc(input logic clk);\n"
      "  logic req;\n"
      "endinterface\n",
      f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->ports.size(), 1u);
}

}  // namespace
