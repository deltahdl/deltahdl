// Annex A.2.3: Declaration lists

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- list_of_variable_identifiers ---
// variable_identifier { variable_dimension }
//     { , variable_identifier { variable_dimension } }
TEST(ParserA23, ListOfVariableIdentifiersSingle) {
  auto r = ParseWithPreprocessor("module m(input logic d); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

TEST(ParserA23, ListOfVariablePortIdentifiersWithDim) {
  auto r = ParseWithPreprocessor(
      "module m(output logic q [1:0] = '{0, 0}); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_FALSE(port.unpacked_dims.empty());
  EXPECT_NE(port.default_value, nullptr);
}

TEST(ParserA212, OutputDefaultValue) {
  // list_of_variable_port_identifiers: port_id [ = constant_expression ]
  auto r = ParseWithPreprocessor("module m(output logic q = 1'b0); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_NE(port.default_value, nullptr);
}

}  // namespace
