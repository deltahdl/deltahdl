// Annex E.5: `delay_mode_path

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- E.3: `delay_mode_path ---
TEST(ParserAnnexE2, AnnexEDelayModePath) {
  auto r = Parse(
      "`delay_mode_path\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

}  // namespace
