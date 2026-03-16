#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ModuleParametersAndPorts, ModuleNonAnsiHeader) {
  auto r = ParseWithPreprocessor(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

TEST(ModuleParametersAndPorts, NonAnsiMultiplePorts) {
  auto r = ParseWithPreprocessor(
      "module m(a, b, c);\n"
      "  input [7:0] a;\n"
      "  output [7:0] b;\n"
      "  inout c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 3u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].direction, Direction::kOutput);
  EXPECT_EQ(ports[2].direction, Direction::kInout);
}

TEST(ModuleParametersAndPorts, NonAnsiSharedType) {
  auto r = ParseWithPreprocessor(
      "module m(a, b);\n"
      "  input [7:0] a, b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].direction, Direction::kInput);
}

TEST(ModuleParametersAndPorts, AnsiPortWithDefault) {
  auto r = ParseWithPreprocessor("module m(input logic a = 1'b0); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_NE(r.cu->modules[0]->ports[0].default_value, nullptr);
}

TEST(ModuleParametersAndPorts, InoutNonAnsi) {
  auto r = ParseWithPreprocessor("module m(a); inout wire [7:0] a; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
}

TEST(ModuleParametersAndPorts, InputNonAnsiMultiple) {
  auto r =
      ParseWithPreprocessor("module m(a, b); input wire [7:0] a, b; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto& port : r.cu->modules[0]->ports) {
    EXPECT_EQ(port.direction, Direction::kInput);
  }
}

TEST(ModuleParametersAndPorts, OutputNonAnsi) {
  auto r = ParseWithPreprocessor("module m(q); output reg q; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

TEST(ModuleParametersAndPorts, OutputNonAnsiUnpackedDim) {
  auto r =
      ParseWithPreprocessor("module m(q); output logic q [3:0]; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

TEST(ModuleParametersAndPorts, InoutWireNetType) {
  auto r = ParseWithPreprocessor("module m(inout wire a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.name, "a");
}

TEST(ModuleParametersAndPorts, InoutPackedDim) {
  auto r = ParseWithPreprocessor("module m(inout [7:0] a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(ModuleParametersAndPorts, OutputVariablePortTypeReg) {
  auto r = ParseWithPreprocessor("module m(output reg q); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

TEST(ModuleParametersAndPorts, RefDeclaration) {
  auto r = ParseWithPreprocessor("module m(ref logic [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kRef);
}

TEST(ModuleParametersAndPorts, VarDataTypeExplicit) {
  auto r = ParseWithPreprocessor(
      "module m(input logic signed [15:0] val); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

TEST(ModuleParametersAndPorts, VarDataTypeInt) {
  auto r = ParseWithPreprocessor("module m(input int count); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

TEST(ModuleParametersAndPorts, NonAnsiSinglePort) {
  auto r = ParseWithPreprocessor("module m(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
}

TEST(ModuleParametersAndPorts, NonAnsiSharedInputDecl) {
  auto r = ParseWithPreprocessor(
      "module m(a, b); input wire [7:0] a, b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  for (auto& port : r.cu->modules[0]->ports) {
    EXPECT_EQ(port.direction, Direction::kInput);
  }
}

TEST(ModuleParametersAndPorts, AnsiSingleInoutWirePort) {
  auto r = ParseWithPreprocessor("module m(inout wire a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInout);
}

TEST(ModuleParametersAndPorts, OutputNetPortType) {
  auto r = ParseWithPreprocessor("module m(output wire q); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

TEST(ModuleParametersAndPorts, NetPortTypeTri) {
  auto r = ParseWithPreprocessor("module m(inout tri [7:0] bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "bus");
}

TEST(ModuleParametersAndPorts, PortWithPackedDim) {
  auto r =
      ParseWithPreprocessor("module m(input logic [15:0] data); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  ASSERT_NE(r.cu->modules[0]->ports[0].data_type.packed_dim_left, nullptr);
}

TEST(ModuleParametersAndPorts, NetPortHeaderWand) {
  auto r = ParseWithPreprocessor("module m(inout wand w); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].data_type.kind, DataTypeKind::kWand);
}

TEST(ModuleParametersAndPorts, NetPortHeaderWor) {
  auto r = ParseWithPreprocessor("module m(inout wor w); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].data_type.kind, DataTypeKind::kWor);
}

TEST(ModuleParametersAndPorts, ParameterPortList) {
  auto r = ParseWithPreprocessor(
      "module m #(parameter int W = 8)(input logic [W-1:0] d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
}

TEST(ModuleParametersAndPorts, EmptyPortList) {
  auto r = ParseWithPreprocessor("module m(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

}  // namespace
