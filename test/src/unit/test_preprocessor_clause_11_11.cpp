// §11.11: Minimum, typical, and maximum delay expressions

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA24, DefparamAssignmentMintypmax) {
  // constant_mintypmax_expression: expr : expr : expr
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  defparam u0.DELAY = 1:2:3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  ASSERT_EQ(item->defparam_assigns.size(), 1u);
}

}  // namespace
