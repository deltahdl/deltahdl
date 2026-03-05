#include "fixture_parser.h"

using namespace delta;

namespace {

// §E.7: delay_mode_zero propagated to CU.
TEST(ParserAnnexE, AnnexEDelayModeZero) {
  auto r = ParseWithPreprocessor(
      "`delay_mode_zero\nmodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->delay_mode_directive, DelayModeDirective::kZero);
}

}  // namespace
