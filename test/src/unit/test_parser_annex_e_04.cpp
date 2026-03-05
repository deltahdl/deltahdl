#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §E.4: `delay_mode_distributed before module.
TEST(ParserAnnexE, AnnexEMultipleDirectives) {
  auto r = ParseWithPreprocessor(
      "`default_decay_time 100\n"
      "`delay_mode_distributed\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

// §E.4: delay_mode_distributed propagated to CU.
TEST(ParserAnnexE2, AnnexEDelayModeDistributed) {
  auto r = ParseWithPreprocessor(
      "`delay_mode_distributed\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->delay_mode_directive, DelayModeDirective::kDistributed);
}

// §E.4: no directive means kNone in CU.
TEST(ParserAnnexE2, AnnexEDelayMode_NoDirective) {
  auto r = ParseWithPreprocessor("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->delay_mode_directive, DelayModeDirective::kNone);
}

}  // namespace
