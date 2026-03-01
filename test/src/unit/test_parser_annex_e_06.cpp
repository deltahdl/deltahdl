// Annex E.6: `delay_mode_unit

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- E.4: `delay_mode_unit ---
TEST(ParserAnnexE2, AnnexEDelayModeUnit) {
  auto r = Parse(
      "`delay_mode_unit\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

}  // namespace
