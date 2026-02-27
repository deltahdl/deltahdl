// Annex A.2.1.2: Port declarations

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- input_declaration ---
// input net_port_type list_of_port_identifiers
// | input variable_port_type list_of_variable_identifiers
TEST(ParserA212, InputNetPortType) {
  auto r = Parse("module m(input wire [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(ParserA212, InputVariablePortTypeLogic) {
  auto r = Parse("module m(input logic [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
}

}  // namespace
