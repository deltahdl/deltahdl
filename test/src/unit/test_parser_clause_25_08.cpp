#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParameterizedInterface, WithParameters) {
  auto r = Parse(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->interfaces[0]->params.empty());
}

TEST(ParameterizedInterface, WithConstants) {
  auto r = Parse(
      "interface ifc;\n"
      "  localparam int DEPTH = 16;\n"
      "  parameter int WIDTH = 8;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(
      CountItemsByKind(r.cu->interfaces[0]->items, ModuleItemKind::kParamDecl),
      1u);
}

}  // namespace
