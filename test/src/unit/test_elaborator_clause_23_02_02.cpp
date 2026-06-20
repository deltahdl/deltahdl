
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

TEST(PortDeclaration, InterfacePortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module m(ifc bus);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->ports[0].name, "bus");
}

TEST(PortDeclaration, ArrayPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input logic [7:0] mem [0:15],\n"
      "  output wire [3:0] bus [4]\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 2u);
}

TEST(PortDeclaration, ModuleWithAtLeast256PortsElaborates) {
  std::string src = "module wide(";
  const int port_count = 300;
  for (int i = 0; i < port_count; ++i) {
    if (i > 0) src += ", ";
    src += "input logic p";
    src += std::to_string(i);
  }
  src += ");\nendmodule\n";
  ElabFixture f;
  auto* design = ElaborateSrc(src, f, "wide");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->ports.size(),
            static_cast<size_t>(port_count));
}

TEST(PortDeclaration, ModuleWithExactly256PortsElaborates) {
  std::string src = "module wide(";
  const int port_count = 256;
  for (int i = 0; i < port_count; ++i) {
    if (i > 0) src += ", ";
    src += "input logic p";
    src += std::to_string(i);
  }
  src += ");\nendmodule\n";
  ElabFixture f;
  auto* design = ElaborateSrc(src, f, "wide");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->ports.size(),
            static_cast<size_t>(port_count));
}

TEST(PortDeclaration, UnpackedArrayOfStructPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input struct packed { logic [7:0] a; logic [7:0] b; } items [0:3]\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->ports[0].type_kind, DataTypeKind::kStruct);
}

}  // namespace
