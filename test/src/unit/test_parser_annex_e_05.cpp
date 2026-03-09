#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserAnnexE2, AnnexEDelayModePath) {
  auto r = ParseWithPreprocessor(
      "`delay_mode_path\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->delay_mode_directive, DelayModeDirective::kPath);
}

}  // namespace
