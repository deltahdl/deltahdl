// §18.13.1: $urandom

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// Annex G - Std package: randomize (§G.4)
// =============================================================================
TEST_F(AnnexHParseTest, AnnexGRandomizeCall) {
  // $urandom and simple randomize() call inside initial block.
  auto* unit = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = $urandom;\n"
      "    x = $urandom();\n"
      "    x = $urandom_range(0, 100);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

}  // namespace
