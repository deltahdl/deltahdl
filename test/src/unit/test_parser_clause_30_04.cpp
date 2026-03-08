#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

  for (auto* si : spec->specify_items) {
    EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  }
}

}
