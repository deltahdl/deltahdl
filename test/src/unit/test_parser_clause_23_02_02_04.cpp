

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- Parsing default values on input ports ---

TEST(DefaultPortValueParsing, InputWithDefaultValue) {
  auto r = Parse("module m(input logic x = 1'b0); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_NE(port.default_value, nullptr);
}

TEST(DefaultPortValueParsing, InputWithBinaryExprDefault) {
  auto r = Parse("module m(input logic [7:0] x = 8'd2 + 8'd3); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_NE(port.default_value, nullptr);
}

TEST(DefaultPortValueParsing, InputWithParameterDefault) {
  auto r = Parse(
      "module m #(parameter P = 8'hFF)\n"
      "          (input logic [7:0] x = P);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(r.cu->modules[0]->ports[0].default_value, nullptr);
}

TEST(DefaultPortValueParsing, MultiplePortsSomeWithDefaults) {
  auto r = Parse(
      "module m(\n"
      "  input logic clk,\n"
      "  input logic rst = 1'b0,\n"
      "  input logic [7:0] data\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].default_value, nullptr);
  EXPECT_NE(r.cu->modules[0]->ports[1].default_value, nullptr);
  EXPECT_EQ(r.cu->modules[0]->ports[2].default_value, nullptr);
}

TEST(DefaultPortValueParsing, AnsiPortWithDefault) {
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

TEST(DefaultPortValueParsing, MultipleInputsAllWithDefaults) {
  auto r = Parse(
      "module m(\n"
      "  input logic a = 1'b0,\n"
      "  input logic b = 1'b1,\n"
      "  input logic [7:0] c = 8'hFF\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 3u);
  EXPECT_NE(r.cu->modules[0]->ports[0].default_value, nullptr);
  EXPECT_NE(r.cu->modules[0]->ports[1].default_value, nullptr);
  EXPECT_NE(r.cu->modules[0]->ports[2].default_value, nullptr);
}

// --- Parser accepts default values on any direction (semantic check is in
//     the elaborator) ---

TEST(DefaultPortValueParsing, OutputWithDefaultValue) {
  auto r = Parse("module m(output logic q = 1'b0); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_NE(port.default_value, nullptr);
}

TEST(DefaultPortValueParsing, InoutWithDefaultValue) {
  auto r = Parse("module m(inout logic x = 1'b0); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(r.cu->modules[0]->ports[0].default_value, nullptr);
}

TEST(DefaultPortValueParsing, RefWithDefaultValue) {
  auto r = Parse("module m(ref logic x = 1'b0); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(r.cu->modules[0]->ports[0].default_value, nullptr);
}

// --- LRM example: bus_conn ---

TEST(DefaultPortValueParsing, LrmExampleBusConn) {
  auto r = Parse(
      "module bus_conn (\n"
      "  output logic [7:0] dataout,\n"
      "  input        [7:0] datain = 8'hFF\n"
      ");\n"
      "  assign dataout = datain;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].default_value, nullptr);
  EXPECT_NE(r.cu->modules[0]->ports[1].default_value, nullptr);
}

}  // namespace
