#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §E.7: `delay_mode_zero before module.
TEST(ParserAnnexE, AnnexEDelayModeZero) {
  auto r = ParseWithPreprocessor(
      "`delay_mode_zero\nmodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

}  // namespace
