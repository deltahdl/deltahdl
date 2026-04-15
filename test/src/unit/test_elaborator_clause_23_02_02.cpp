
#include "fixture_elaborator.h"

namespace {

TEST(PortDeclaration, StructPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input struct packed { logic [7:0] a; logic [7:0] b; } data_in,\n"
      "  output logic [15:0] data_out\n"
      ");\n"
      "  assign data_out = data_in;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->ports[0].type_kind, DataTypeKind::kStruct);
}

TEST(PortDeclaration, UnionPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input union packed { logic [31:0] word; logic [3:0][7:0] bytes; } u\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->ports[0].type_kind, DataTypeKind::kUnion);
}

TEST(PortDeclaration, EventPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input event e);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->ports[0].type_kind, DataTypeKind::kEvent);
}

}  // namespace
