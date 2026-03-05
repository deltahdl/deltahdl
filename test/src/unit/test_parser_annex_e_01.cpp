#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §E.1: all six directives followed by a module — parser sees clean output.
TEST(ParserAnnexE2, AnnexEAllDirectivesCombined) {
  auto r = ParseWithPreprocessor(
      "`default_decay_time 10\n"
      "`default_trireg_strength 100\n"
      "`delay_mode_distributed\n"
      "`delay_mode_path\n"
      "`delay_mode_unit\n"
      "`delay_mode_zero\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

}  // namespace
