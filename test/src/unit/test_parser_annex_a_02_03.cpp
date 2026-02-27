// Annex A.2.3: Declaration lists

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- list_of_variable_port_identifiers ---
// port_identifier { variable_dimension } [ = constant_expression ]
//     { , port_identifier { variable_dimension } [ = constant_expression ] }
TEST(ParserA23, ListOfVariablePortIdentifiersSingle) {
  auto r = Parse("module m(output logic q = 1'b0); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_NE(port.default_value, nullptr);
}

}  // namespace
