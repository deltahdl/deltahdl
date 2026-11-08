#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

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
      "module m(input var event e);\n"
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

TEST(PortDeclaration, EnumPortElaboratesAsANetWhenThePortKindIsOmitted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input enum { RED, GREEN, BLUE } color\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  const auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.type_kind, DataTypeKind::kEnum);
  EXPECT_EQ(port.width, 32u);
  EXPECT_FALSE(port.is_var);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 2, "6.7.1"));
}

TEST(PortDeclaration, VarEnumPortElaboratesAsAVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input var enum { RED, GREEN, BLUE } color\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  const auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.name, "color");
  EXPECT_EQ(port.type_kind, DataTypeKind::kEnum);
  EXPECT_EQ(port.width, 32u);
  EXPECT_TRUE(port.is_var);
}

TEST(PortDeclaration, VarStructPortElaboratesAsAVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input var struct packed { logic [7:0] a; logic [7:0] b; } s\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  const auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.name, "s");
  EXPECT_EQ(port.type_kind, DataTypeKind::kStruct);
  EXPECT_EQ(port.width, 16u);
  EXPECT_TRUE(port.is_var);
}

TEST(PortDeclaration, EnumPortWithAFourStateBaseIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input enum logic [1:0] { RED, GREEN, BLUE } color\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PortDeclaration, TwoStateInputPortIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(\n"
      "  input bit [7:0] data\n"
      ");\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 2, "6.7.1"));
}

TEST(PortDeclaration, TwoStateOutputPortIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  output bit [7:0] data\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

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

void ExpectSolePortUnpackedBounds(const char* src, int64_t left,
                                  int64_t right) {
  SCOPED_TRACE(src);
  ElabFixture f;
  auto* design = ElaborateSrc(src, f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  const auto& port = design->top_modules[0]->ports[0];
  ASSERT_EQ(port.unpacked_dims.size(), 1u);
  EXPECT_EQ(port.unpacked_dims[0].left, left);
  EXPECT_EQ(port.unpacked_dims[0].right, right);
}

void ExpectSolePortUnpackedSize(const char* src, uint32_t size) {
  SCOPED_TRACE(src);
  ElabFixture f;
  auto* design = ElaborateSrc(src, f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  const auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.num_unpacked_dims, 1u);
  ASSERT_EQ(port.unpacked_dim_sizes.size(), 1u);
  EXPECT_EQ(port.unpacked_dim_sizes[0], size);
}

TEST(PortDeclaration, UnpackedArrayPortRecordsItsAddressBounds) {
  ExpectSolePortUnpackedBounds(
      "module m(\n"
      "  input logic [7:0] mem [1:4]\n"
      ");\n"
      "endmodule\n",
      1, 4);
}

TEST(PortDeclaration, UnpackedArrayPortDistinguishesTheSizeFormFromARange) {
  ExpectSolePortUnpackedBounds(
      "module m(\n"
      "  input logic [7:0] mem [4]\n"
      ");\n"
      "endmodule\n",
      0, 3);
}

TEST(PortDeclaration, DescendingUnpackedArrayPortRecordsItsDeclaredOrder) {
  ExpectSolePortUnpackedBounds(
      "module m(\n"
      "  input logic [7:0] mem [4:1]\n"
      ");\n"
      "endmodule\n",
      4, 1);
}

TEST(PortDeclaration, ParameterSizedUnpackedArrayPortFolds) {
  ExpectSolePortUnpackedSize(
      "module m #(parameter int N = 4) (\n"
      "  input logic [7:0] mem [N]\n"
      ");\n"
      "endmodule\n",
      4);
}

TEST(PortDeclaration, ParameterBoundedUnpackedArrayPortFolds) {
  ExpectSolePortUnpackedBounds(
      "module m #(parameter int N = 4) (\n"
      "  input logic [7:0] mem [1:N]\n"
      ");\n"
      "endmodule\n",
      1, 4);
}

TEST(PortDeclaration, BodyParameterSizedUnpackedArrayPortFolds) {
  ExpectSolePortUnpackedSize(
      "module m(mem);\n"
      "  parameter int N = 4;\n"
      "  input logic [7:0] mem [N];\n"
      "endmodule\n",
      4);
}

}  // namespace
