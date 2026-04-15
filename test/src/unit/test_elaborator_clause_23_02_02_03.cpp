
#include "fixture_elaborator.h"

namespace {

TEST(PortKindDataTypeDirection, OmittedDirectionElaboratesToInout) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m(wire x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->ports[0].direction, Direction::kInout);
  EXPECT_EQ(design->top_modules[0]->ports[0].width, 1u);
}

TEST(PortKindDataTypeDirection, OmittedTypeElaboratesAsLogicWidth1) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m(input x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(port.width, 1u);
}

TEST(PortKindDataTypeDirection, InheritedPortElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input logic [7:0] x, y);\n"
      "endmodule",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 2u);
  auto& py = design->top_modules[0]->ports[1];
  EXPECT_EQ(py.direction, Direction::kInput);
  EXPECT_EQ(py.type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(py.width, 8u);
}

TEST(PortKindDataTypeDirection, OutputExplicitIntegerElaboratesWidth32) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(output integer x);\n"
      "endmodule",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.type_kind, DataTypeKind::kInteger);
  EXPECT_EQ(port.width, 32u);
}

TEST(PortKindDataTypeDirection, SignedImplicitTypeElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(output signed [5:0] x);\n"
      "endmodule",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(port.width, 6u);
  EXPECT_TRUE(port.is_signed);
}

}  // namespace
