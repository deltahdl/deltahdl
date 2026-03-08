#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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
  auto r = ParseWithPreprocessor("module m(output logic q = 1'b0); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_NE(port.default_value, nullptr);
}

TEST(ParserA23, ListOfPortIdentifiersWithUnpackedDim) {
  auto r = ParseWithPreprocessor("module m(inout logic a [3:0]); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->ports[0].unpacked_dims.empty());
}

TEST(ParserA23, ListOfVariableIdentifiersMultipleAnsi) {
  auto r = ParseWithPreprocessor(
      "module m(input logic a, input logic b, input logic c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 3u);
  for (auto& port : r.cu->modules[0]->ports) {
    EXPECT_EQ(port.direction, Direction::kInput);
  }
}

TEST(ParserA23, ListOfVariableIdentifiersWithDim) {
  auto r = ParseWithPreprocessor("module m(input logic d [3:0]); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->ports[0].unpacked_dims.empty());
}

TEST(ParserA23, ListOfVariablePortIdentifiersMultipleAnsi) {
  auto r = ParseWithPreprocessor(
      "module m(output logic a = 1'b0, output logic b = 1'b1); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_NE(r.cu->modules[0]->ports[0].default_value, nullptr);
  EXPECT_NE(r.cu->modules[0]->ports[1].default_value, nullptr);
}

}  // namespace
