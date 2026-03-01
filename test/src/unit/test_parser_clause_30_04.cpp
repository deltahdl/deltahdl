// §30.4: Module path declarations

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.2 Multiple path declarations in one specify block
// =============================================================================
TEST(ParserA702, MultiplePathDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "    (c, d *> e) = 10;\n"
      "    (posedge clk => q) = 3;\n"
      "    if (en) (a => b) = 8;\n"
      "    ifnone (a => b) = 15;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 5u);
  // All should be path declarations
  for (auto* si : spec->specify_items) {
    EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  }
}

}  // namespace
