
#include "fixture_elaborator.h"

namespace {

void ExpectWideModuleElaborates(int port_count) {
  std::string src = "module wide(";
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

// §23.2.2: a port may be a *variable* of any allowed data type. The mh1
// example illustrates this with var-qualified integer and real ports. Those
// var-typed scalar forms are only exercised at parse time elsewhere; observe
// here that they survive elaboration with their data-type kind preserved and
// the non-net (variable) flag set, alongside a struct output port.
TEST(PortDeclaration, VarTypedScalarPortsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module mh1(\n"
      "  input var int in1,\n"
      "  input var shortreal in2,\n"
      "  output struct packed { logic [7:0] a; logic [7:0] b; } out\n"
      ");\n"
      "endmodule\n",
      f, "mh1");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 3u);
  const auto& ports = design->top_modules[0]->ports;
  EXPECT_EQ(ports[0].type_kind, DataTypeKind::kInt);
  EXPECT_TRUE(ports[0].is_var);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].type_kind, DataTypeKind::kShortreal);
  EXPECT_TRUE(ports[1].is_var);
  EXPECT_EQ(ports[2].type_kind, DataTypeKind::kStruct);
  EXPECT_EQ(ports[2].direction, Direction::kOutput);
}

// §23.2.2: an enumeration is an admitted port data type. Observe that an inline
// enum port survives elaboration as an enum-kind variable port with the base
// (int) width.
TEST(PortDeclaration, EnumPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input enum { RED, GREEN, BLUE } color\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  const auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.type_kind, DataTypeKind::kEnum);
  EXPECT_EQ(port.width, 32u);
  EXPECT_TRUE(port.is_var);
}

// §23.2.2: a port data type may carry multiple packed dimensions. The
// elaborated width is the product of the two packed dimensions (4 * 8) with no
// unpacked dimension.
TEST(PortDeclaration, PackedArrayPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input logic [3:0][7:0] data\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  const auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(port.width, 32u);
  EXPECT_EQ(port.num_unpacked_dims, 0u);
}

// §23.2.2: a port may be a multidimensional (2-D) unpacked array. Both unpacked
// dimensions are folded to their element counts (4 and 2) during elaboration.
TEST(PortDeclaration, MultiDimUnpackedArrayPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input logic [7:0] mem [0:3][0:1]\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  const auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.num_unpacked_dims, 2u);
  ASSERT_EQ(port.unpacked_dim_sizes.size(), 2u);
  EXPECT_EQ(port.unpacked_dim_sizes[0], 4u);
  EXPECT_EQ(port.unpacked_dim_sizes[1], 2u);
}

TEST(PortDeclaration, ModuleWithAtLeast256PortsElaborates) {
  ExpectWideModuleElaborates(300);
}

TEST(PortDeclaration, ModuleWithExactly256PortsElaborates) {
  ExpectWideModuleElaborates(256);
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
