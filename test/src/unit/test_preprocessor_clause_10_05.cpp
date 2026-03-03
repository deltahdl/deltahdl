// §10.5: Variable declaration assignment (variable initialization)

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// LRM section 10.5 -- Variable declaration assignment
// =============================================================================
TEST(ParserSection10, VarDeclAssignment) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  int x = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  auto* item = mod->items[0];
  EXPECT_EQ(item->name, "x");
  EXPECT_NE(item->init_expr, nullptr);
}

}  // namespace
