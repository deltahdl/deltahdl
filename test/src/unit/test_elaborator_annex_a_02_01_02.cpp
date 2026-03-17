#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(PortDeclElaboration, InputPortElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic [7:0] d);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].name, "d");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
}

TEST(PortDeclElaboration, OutputPortElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(output logic [3:0] q);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].name, "q");
  EXPECT_EQ(mod->ports[0].direction, Direction::kOutput);
}

TEST(PortDeclElaboration, InoutPortElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(inout wire [7:0] bus);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].name, "bus");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInout);
}

TEST(PortDeclElaboration, RefPortElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(ref logic [7:0] d);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].name, "d");
  EXPECT_EQ(mod->ports[0].direction, Direction::kRef);
}

TEST(PortDeclElaboration, AllDirectionsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic a, output logic b,\n"
      "         inout wire c, ref logic d);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 4u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(mod->ports[2].direction, Direction::kInout);
  EXPECT_EQ(mod->ports[3].direction, Direction::kRef);
}

TEST(PortDeclElaboration, InputIntegerTypePortWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input int val);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].name, "val");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[0].width, 32u);
}

}  // namespace
