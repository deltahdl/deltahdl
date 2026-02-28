// Annex E.7: `delay_mode_zero

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// Annex E.7 -- `delay_mode_zero
// =============================================================================
TEST(ParserAnnexE, AnnexEDelayModeZero) {
  auto r = Parse("`delay_mode_zero\nmodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

}  // namespace
