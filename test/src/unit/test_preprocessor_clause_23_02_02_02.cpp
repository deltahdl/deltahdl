// §23.2.2.2: ANSI style list of port declarations

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Module with both parameters and ports
TEST(SourceText, ParamsAndPorts) {
  auto r = ParseWithPreprocessor(
      "module m #(parameter int W = 8)(input logic [W-1:0] data,\n"
      "                                 output logic valid);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "W");
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "data");
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "valid");
}

}  // namespace
