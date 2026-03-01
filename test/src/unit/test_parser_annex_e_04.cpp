// Annex E.4: `delay_mode_distributed

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// Annex E.4 -- `delay_mode_distributed
// =============================================================================
TEST(ParserAnnexE, AnnexEMultipleDirectives) {
  auto r = Parse(
      "`default_decay_time 100\n"
      "`delay_mode_distributed\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

// --- E.2: `delay_mode_distributed ---
TEST(ParserAnnexE2, AnnexEDelayModeDistributed) {
  auto r = Parse(
      "`delay_mode_distributed\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

}  // namespace
