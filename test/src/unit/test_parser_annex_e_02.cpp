// Annex E.2: `default_decay_time

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// Annex E.2 -- `default_decay_time
// =============================================================================
TEST(ParserAnnexE, AnnexEDefaultDecayTime) {
  auto r = Parse("`default_decay_time 10\nmodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

}  // namespace
