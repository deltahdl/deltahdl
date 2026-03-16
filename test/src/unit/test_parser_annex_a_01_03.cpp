#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ModuleParametersAndPorts, NonAnsiPortListMultiple) {
  auto r = Parse("module m(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "b");
  EXPECT_EQ(r.cu->modules[0]->ports[2].name, "c");
}

TEST(ModuleParametersAndPorts, NonAnsiPortsBasic) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "  assign b = a;\n"
      "endmodule\n");
  VerifyTwoPortModule(r, "a", Direction::kInput, "b", Direction::kOutput);
}

TEST(ModuleParametersAndPorts, NonAnsiInputWithPackedDims) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input [7:0] a;\n"
      "  output reg b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  EXPECT_EQ(mod->ports[0].name, "a");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_NE(mod->ports[0].data_type.packed_dim_left, nullptr);
}

TEST(ModuleParametersAndPorts, NonAnsiOutputRegType) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input [7:0] a;\n"
      "  output reg b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  EXPECT_EQ(mod->ports[1].name, "b");
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(mod->ports[1].data_type.kind, DataTypeKind::kReg);
}

TEST(ModuleParametersAndPorts, NonAnsiPortsMixed) {
  auto r = Parse(
      "module m(a, b, c, d);\n"
      "  input a, b;\n"
      "  output [3:0] c;\n"
      "  inout d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 4);
  struct Expected {
    const char* name;
    Direction dir;
  };
  Expected expected[] = {
      {"a", Direction::kInput},
      {"b", Direction::kInput},
      {"c", Direction::kOutput},
      {"d", Direction::kInout},
  };
  for (size_t i = 0; i < 4; ++i) {
    EXPECT_EQ(mod->ports[i].name, expected[i].name);
    EXPECT_EQ(mod->ports[i].direction, expected[i].dir);
  }
  EXPECT_NE(mod->ports[2].data_type.packed_dim_left, nullptr);
}

TEST(ModuleParametersAndPorts, NonAnsiPortDeclarations) {
  auto r = Parse(
      "module m (a, b, y);\n"
      "  input a, b;\n"
      "  output y;\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);

  EXPECT_TRUE(
      ParseOk("module m (a, d); input [15:0] a; inout [7:0] d; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m (a, b); inout [7:0] a; inout [7:0] b; endmodule\n"));
}

TEST(ModuleParametersAndPorts, NonAnsiInoutPort) {
  auto r = Parse(
      "module m(bus);\n"
      "  inout [7:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1);
  EXPECT_EQ(mod->ports[0].name, "bus");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInout);
  EXPECT_NE(mod->ports[0].data_type.packed_dim_left, nullptr);
}

TEST(ModuleParametersAndPorts, NonAnsiMultiplePortsSameDir) {
  auto r = Parse(
      "module m(x, y, z);\n"
      "  output x, y, z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 3);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(mod->ports[i].direction, Direction::kOutput);
  }
}

TEST(ModuleParametersAndPorts, NonAnsiPorts) {
  auto r = Parse(
      "module m(a, b, y);\n"
      "  input a, b;\n"
      "  output y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_GE(r.cu->modules[0]->ports.size(), 3u);
}

TEST(ModuleParametersAndPorts, AnsiPortDirections) {
  auto r = Parse(
      "module m (input logic a, output logic y,\n"
      "          inout wire [7:0] data, ref logic [3:0] r);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 4u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "y");
  EXPECT_EQ(r.cu->modules[0]->ports[2].direction, Direction::kInout);
  EXPECT_EQ(r.cu->modules[0]->ports[2].name, "data");
  EXPECT_EQ(r.cu->modules[0]->ports[3].direction, Direction::kRef);
  EXPECT_EQ(r.cu->modules[0]->ports[3].name, "r");
}

TEST(ModuleParametersAndPorts, EmptyPortsAndMiscVariants) {
  auto r1 = Parse("module m (); endmodule\n");
  ASSERT_NE(r1.cu, nullptr);
  EXPECT_FALSE(r1.has_errors);
  EXPECT_EQ(r1.cu->modules[0]->ports.size(), 0u);
  auto r2 = Parse("module m; endmodule\n");
  ASSERT_NE(r2.cu, nullptr);
  EXPECT_FALSE(r2.has_errors);
  EXPECT_EQ(r2.cu->modules[0]->ports.size(), 0u);
  EXPECT_TRUE(ParseOk("module m (.*); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m (input int x = 10); endmodule\n"));

  EXPECT_TRUE(ParseOk("module m (input var int in1); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m (output reg [7:0] q); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m (input signed [7:0] s); endmodule\n"));

  EXPECT_TRUE(ParseOk("macromodule mm; endmodule\n"));
}

TEST(ModuleParametersAndPorts, AnsiPortsInputOutput) {
  auto r = Parse(
      "module m(input logic clk, input logic rst, output logic q);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 3u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[0].name, "clk");
  EXPECT_EQ(mod->ports[2].direction, Direction::kOutput);
  EXPECT_EQ(mod->ports[2].name, "q");
}

TEST(ModuleParametersAndPorts, AnsiPortsInout) {
  auto r = Parse(
      "module m(inout wire [7:0] data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInout);
  EXPECT_EQ(mod->ports[0].name, "data");
}

TEST(ModuleParametersAndPorts, AnsiHeaderWithParams) {
  auto r = Parse(
      "module m #(parameter N = 8) (input logic [N-1:0] data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  ASSERT_EQ(mod->params.size(), 1);
  EXPECT_EQ(mod->params[0].first, "N");
  ASSERT_EQ(mod->ports.size(), 1);
  EXPECT_EQ(mod->ports[0].name, "data");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
}

TEST(ModuleParametersAndPorts, ModuleWithPortsAndAssign) {
  auto r = Parse(
      "module mux(input logic a, input logic b, input logic sel, output logic "
      "y);\n"
      "  assign y = sel ? b : a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  struct Expected {
    Direction dir;
    const char* name;
  };
  Expected expected[] = {
      {Direction::kInput, "a"},
      {Direction::kInput, "b"},
      {Direction::kInput, "sel"},
      {Direction::kOutput, "y"},
  };
  ASSERT_EQ(mod->ports.size(), std::size(expected));
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(mod->ports[i].direction, expected[i].dir) << "port " << i;
    EXPECT_EQ(mod->ports[i].name, expected[i].name) << "port " << i;
  }
}

TEST(ModuleParametersAndPorts, VariablePortHeader) {
  auto r = Parse("module m(input logic [3:0] sel); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "sel");
}

TEST(ModuleParametersAndPorts, InputVariablePortTypeVar) {
  auto r = Parse("module m(input var logic d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

TEST(ModuleParametersAndPorts, AnsiPortsWithDefaultType) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
}

TEST(ModuleParametersAndPorts, AnsiPortDeclarations) {
  auto r = Parse(
      "module m(\n"
      "  input  logic       clk,\n"
      "  input  logic       rst,\n"
      "  output logic [7:0] data\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 3u);
}

TEST(ModuleParametersAndPorts, AllPortDirections) {
  auto r = Parse(
      "module m(\n"
      "  input  logic a,\n"
      "  output logic b,\n"
      "  inout  wire  c,\n"
      "  ref    logic d\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 4u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].direction, Direction::kOutput);
  EXPECT_EQ(ports[2].direction, Direction::kInout);
  EXPECT_EQ(ports[3].direction, Direction::kRef);
}

TEST(ModuleParametersAndPorts, AnsiPortUnpackedDim) {
  auto r = Parse(
      "module m(\n"
      "  input logic [7:0] data [4]\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleParametersAndPorts, InterfacePortHeader) {
  auto r = Parse(
      "module m(bus_if.master bus);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleParametersAndPorts, AnsiPortWithDefault) {
  auto r = Parse(
      "module m(\n"
      "  input logic clk,\n"
      "  input logic rst = 0\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_NE(r.cu->modules[0]->ports[1].default_value, nullptr);
}

TEST(ModuleParametersAndPorts, ModuleWithAnsiPortDeclarations) {
  auto r = Parse(
      "module m(input wire a, b, sel, output logic y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.cu->modules[0]->ports.empty());
}

TEST(ModuleParametersAndPorts, InoutImplicitType) {
  auto r = Parse("module m(inout a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
}

TEST(ModuleParametersAndPorts, InterfacePortParsedAsNonAnsi) {
  auto r = Parse("module m(a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kNone);
}

TEST(ModuleParametersAndPorts, RefUnpackedDim) {
  auto r = Parse("module m(ref int arr [4]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ModuleParametersAndPorts, InputNetPortType) {
  auto r = Parse("module m(input wire [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(ModuleParametersAndPorts, InputVariablePortTypeLogic) {
  auto r = Parse("module m(input logic [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
}

TEST(ModuleParametersAndPorts, NetAsInputPort) {
  auto r = Parse(
      "module t(input wire [7:0] data_in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 1u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kWire);
  EXPECT_TRUE(ports[0].data_type.is_net);
  EXPECT_EQ(ports[0].name, "data_in");
  ASSERT_NE(ports[0].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(ports[0].data_type.packed_dim_left->int_val, 7u);
}

TEST(ModuleParametersAndPorts, VarAsOutputPort) {
  auto r = Parse(
      "module t(output logic [15:0] result);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 1u);
  EXPECT_EQ(ports[0].direction, Direction::kOutput);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(ports[0].name, "result");
  ASSERT_NE(ports[0].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(ports[0].data_type.packed_dim_left->int_val, 15u);
}

TEST(ModuleParametersAndPorts, ImplicitTypePortDecl) {
  auto r = Parse("module m(input [3:0] a, output [7:0] b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  auto& ports = r.cu->modules[0]->ports;
  std::string expected_names[] = {"a", "b"};
  ASSERT_EQ(ports.size(), std::size(expected_names));
  for (size_t i = 0; i < std::size(expected_names); ++i) {
    EXPECT_EQ(ports[i].name, expected_names[i]) << "port " << i;
    EXPECT_EQ(ports[i].data_type.kind, DataTypeKind::kLogic) << "port " << i;
  }
}

TEST(ModuleParametersAndPorts, IntegerTypesAsPortDecls) {
  auto r = Parse(
      "module m(input int a, output byte b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(ports[0].name, "a");
  EXPECT_EQ(ports[1].direction, Direction::kOutput);
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(ports[1].name, "b");
}

TEST(ModuleParametersAndPorts, LongintShortintAsPorts) {
  auto r = Parse(
      "module m(input longint addr, output shortint result);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(ports[0].name, "addr");
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kShortint);
  EXPECT_EQ(ports[1].name, "result");
}

TEST(ModuleParametersAndPorts, LogicPackedDimsAsPort) {
  auto r = Parse(
      "module m(input logic [7:0] data, output logic [15:0] addr);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(ports[0].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(ports[0].data_type.packed_dim_left->int_val, 7u);
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(ports[1].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(ports[1].data_type.packed_dim_left->int_val, 15u);
}

TEST(ModuleParametersAndPorts, IntegerAsPort) {
  auto r = Parse(
      "module m(input integer idx);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 1u);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kInteger);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
}

TEST(ModuleParametersAndPorts, VarImplicitInPort) {
  EXPECT_TRUE(
      ParseOk("module t(input var [7:0] data_in);\n"
              "endmodule\n"));
}

TEST(ModuleParametersAndPorts, ShortrealInPort) {
  EXPECT_TRUE(
      ParseOk("module m (input var shortreal in_val,\n"
              "          output var shortreal out_val);\n"
              "  assign out_val = in_val;\n"
              "endmodule\n"));
}

TEST(ModuleParametersAndPorts, InoutUnpackedDim) {
  auto r = Parse("module m(inout logic a [3:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ModuleParametersAndPorts, OutputUnpackedDim) {
  auto r = Parse("module m(output logic q [1:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ModuleParametersAndPorts, InputUnpackedDim) {
  auto r = Parse("module m(input logic d [3:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ModuleParametersAndPorts, ModuleWithParameters) {
  auto r = Parse(
      "module m #(parameter WIDTH = 8, parameter DEPTH = 16)(\n"
      "  input logic [WIDTH-1:0] data_in,\n"
      "  output logic [WIDTH-1:0] data_out\n"
      ");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  ASSERT_EQ(mod->params.size(), 2u);
  EXPECT_EQ(mod->params[0].first, "WIDTH");
  EXPECT_EQ(mod->params[1].first, "DEPTH");
  ASSERT_EQ(mod->ports.size(), 2u);
}

TEST(ModuleParametersAndPorts, TwoParamsOnePort) {
  auto r = Parse(
      "module m #(parameter W = 8, parameter D = 4)(\n"
      "  input logic [W-1:0] data\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->params.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 1u);
}

TEST(ModuleParametersAndPorts, EmptyParamPortList) {
  auto r = Parse("module m #(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->params.empty());
}

TEST(ModuleParametersAndPorts, LocalparamInParamPortList) {
  auto r = Parse(
      "module m #(parameter W = 8, localparam D = W*2)(\n"
      "  input logic [D-1:0] data\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleParametersAndPorts, ModuleEmptyPortList) {
  auto r = Parse("module m(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

TEST(ModuleParametersAndPorts, AnsiHeaderEmptyParenPorts) {
  auto r = Parse("module m (); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

TEST(ModuleParametersAndPorts, ParamOmitValueInPortList) {
  auto r = Parse(
      "module m #(parameter int W) (input [W-1:0] d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleParametersAndPorts, TypeParamOmitTypeInPortList) {
  auto r = Parse(
      "module m #(parameter type T) ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleParametersAndPorts, NetPortHeaderTri) {
  auto r = Parse("module m(input tri [7:0] bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kTri);
}

TEST(ModuleParametersAndPorts, NetPortHeaderWand) {
  auto r = Parse("module m(inout wand w); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].data_type.kind, DataTypeKind::kWand);
}

TEST(ModuleParametersAndPorts, NetPortHeaderWor) {
  auto r = Parse("module m(inout wor w); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].data_type.kind, DataTypeKind::kWor);
}

TEST(ModuleParametersAndPorts, NetPortHeaderSupply) {
  EXPECT_TRUE(ParseOk("module m(input supply0 s0); endmodule"));
  EXPECT_TRUE(ParseOk("module m(input supply1 s1); endmodule"));
}

TEST(ModuleParametersAndPorts, NetPortHeaderUwire) {
  auto r = Parse("module m(input uwire w); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].data_type.kind, DataTypeKind::kUwire);
}

TEST(ModuleParametersAndPorts, BareDataTypeParamDecl) {
  auto r = Parse("module m #(parameter int A = 1, int B = 2)(); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "A");
  EXPECT_EQ(r.cu->modules[0]->params[1].first, "B");
}

TEST(ModuleParametersAndPorts, TypeParamNoKeyword) {
  auto r = Parse("module m #(type T = int)(); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "T");
}

TEST(ModuleParametersAndPorts, MixedParamPortDecls) {
  auto r = Parse(
      "module m #(parameter int A = 1, localparam int B = 5, type T = logic)\n"
      "(); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 3u);
}

TEST(ModuleParametersAndPorts, NonAnsiRefPort) {
  auto r = Parse(
      "module m(d);\n"
      "  ref logic [7:0] d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kRef);
}

TEST(ModuleParametersAndPorts, WildcardPortList) {
  auto r = Parse("module m(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_wildcard_ports);
}

TEST(ModuleParametersAndPorts, PortDeclSignedPackedDims) {
  auto r = Parse("module m(input signed [7:0] s); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(ModuleParametersAndPorts, AnsiPortMultipleUnpackedDims) {
  auto r = Parse("module m(input logic data [4][8]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->modules[0]->ports[0].unpacked_dims.size(), 2u);
}

TEST(ModuleParametersAndPorts, ErrorMissingPortListClose) {
  EXPECT_FALSE(ParseOk("module m(input logic a endmodule"));
}

TEST(ModuleParametersAndPorts, ErrorMissingParamListClose) {
  EXPECT_FALSE(ParseOk("module m #(parameter int W endmodule"));
}

TEST(ModuleParametersAndPorts, ErrorTrailingCommaInPortList) {
  EXPECT_FALSE(ParseOk("module m(input a,); endmodule"));
}

TEST(ModuleParametersAndPorts, ErrorTrailingCommaInParamList) {
  EXPECT_FALSE(ParseOk("module m #(parameter int A,)(); endmodule"));
}

}  // namespace
