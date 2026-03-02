// §3.5: Interfaces

#include "fixture_parser.h"

using namespace delta;

namespace {

// §3.5:
TEST(ParserClause03, Cl3_5_ParametersConstantsVariables) {
  auto r = ParseWithPreprocessor(
      "interface ifc #(parameter WIDTH = 8);\n"
      "  localparam DEPTH = 16;\n"
      "  logic [WIDTH-1:0] data;\n"
      "  wire valid;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_GE(r.cu->interfaces[0]->items.size(), 2u);
}

}  // namespace
