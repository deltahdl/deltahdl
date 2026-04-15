#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DefaultPortValueParsing, AnsiPortWithDefault) {
  auto r = ParseWithPreprocessor("module m(input logic a = 1'b0); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_NE(r.cu->modules[0]->ports[0].default_value, nullptr);
}

TEST(DefaultPortValueParsing, OutputDefaultValue) {
  auto r = ParseWithPreprocessor("module m(output logic q = 1'b0); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_NE(port.default_value, nullptr);
}

TEST(DefaultPortValueParsing, InputWithParameterDefault) {
  auto r = ParseWithPreprocessor(
      "module m #(parameter P = 8'hFF)\n"
      "          (input logic [7:0] x = P);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(r.cu->modules[0]->ports[0].default_value, nullptr);
}

TEST(DefaultPortValueParsing, MultiplePortsSomeWithDefaults) {
  auto r = ParseWithPreprocessor(
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

TEST(DefaultPortValueParsing, LrmExampleBusConn) {
  auto r = ParseWithPreprocessor(
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
