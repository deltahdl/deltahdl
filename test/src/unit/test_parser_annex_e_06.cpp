#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §E.6: `delay_mode_unit before module.
TEST(ParserAnnexE2, AnnexEDelayModeUnit) {
  auto r = ParseWithPreprocessor(
      "`delay_mode_unit\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

}  // namespace
