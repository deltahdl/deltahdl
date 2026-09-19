#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_specify.h"

using namespace delta;

namespace {

TEST(MultiplePathDeclarationParsing, MultipleSourceDestPorts) {
  auto sp = ParseSpecifySingle(
      "module m(input a, b, c, output x, y);\n"
      "  specify\n"
      "    (a, b, c *> x, y) = 12;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  VerifyFullPathPorts(si, {"a", "b", "c"}, {"x", "y"});
}

}  // namespace
