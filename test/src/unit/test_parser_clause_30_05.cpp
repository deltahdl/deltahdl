// §30.5: Assigning delays to module paths

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.4 path_delay_value — bare vs parenthesized
// =============================================================================
// path_delay_value ::= list_of_path_delay_expressions (bare form)
TEST(ParserA704, PathDelayValueBare) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
}

}  // namespace
