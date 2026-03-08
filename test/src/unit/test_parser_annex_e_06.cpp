#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserAnnexE2, AnnexEDelayModeUnit) {
  auto r = ParseWithPreprocessor(
      "`delay_mode_unit\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->delay_mode_directive, DelayModeDirective::kUnit);
}

}
