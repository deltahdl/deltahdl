// §25.3.2

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(InterfaceDeclaration, WithVariables) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic req, gnt;\n"
      "  logic [7:0] addr, data;\n"
      "  logic [1:0] mode;\n"
      "  logic start, rdy;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->interfaces[0]->items.empty());
}

}  // namespace
