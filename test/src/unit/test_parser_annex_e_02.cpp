#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §E.2: `default_decay_time before module.
TEST(ParserAnnexE, AnnexEDefaultDecayTime) {
  auto r = ParseWithPreprocessor(
      "`default_decay_time 10\nmodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

}  // namespace
