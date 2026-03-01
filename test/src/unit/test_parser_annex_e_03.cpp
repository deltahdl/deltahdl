// Annex E.3: `default_trireg_strength

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// Annex E -- Optional compiler directives
// =============================================================================
// --- E.1: `default_trireg_strength ---
TEST(ParserAnnexE2, AnnexEDefaultTriregStrength) {
  auto r = Parse(
      "`default_trireg_strength 50\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

}  // namespace
