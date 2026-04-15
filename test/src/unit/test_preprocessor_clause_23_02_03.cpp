#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParameterizedModules, AnsiHeaderWithParamsThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m #(parameter int W = 8)(input logic [W-1:0] d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 1u);
}

TEST(ParameterizedModules, NonAnsiHeaderWithParamsThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m #(parameter int W = 4)(a, b);\n"
      "  input [W-1:0] a;\n"
      "  output [W-1:0] b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

TEST(ParameterizedModules, LocalparamDerivedFromParamThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m #(parameter num_code_bits = 3,\n"
      "           localparam num_out_bits = 1 << num_code_bits)\n"
      "  (input [num_code_bits-1:0] A,\n"
      "   output reg [num_out_bits-1:0] Y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 2u);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

}  // namespace
