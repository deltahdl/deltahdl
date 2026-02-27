// §23.2.2.2: ANSI style list of port declarations

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- data_type_or_implicit ---
// data_type | implicit_data_type
// --- implicit_data_type ---
// [signing] {packed_dimension}
TEST(ParserA221, ImplicitDataType) {
  // Implicit data type with just packed dimension
  auto r = Parse("module m(input [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(ParserA221, ImplicitDataTypeSigned) {
  // signed [7:0]
  auto r = Parse("module m(input signed [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_TRUE(port.data_type.is_signed);
}

TEST(ParserA212, InoutUnpackedDim) {
  auto r = Parse("module m(inout logic a [3:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ParserA212, OutputUnpackedDim) {
  auto r = Parse("module m(output logic q [1:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ParserA212, InputUnpackedDim) {
  // list_of_variable_identifiers: variable_identifier { variable_dimension }
  auto r = Parse("module m(input logic d [3:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

}  // namespace
