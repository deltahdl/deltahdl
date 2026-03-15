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

TEST(InterfacePorts, SimpleBusWithClkPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "  logic [7:0] addr, data;\n"
      "  logic [1:0] mode;\n"
      "  logic start, rdy;\n"
      "endinterface\n",
      f, "simple_bus");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
