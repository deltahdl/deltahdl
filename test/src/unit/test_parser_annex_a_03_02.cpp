// Annex A.3.2: Primitive strengths

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// -----------------------------------------------------------------------------
// Production #2: pullup_strength
// pullup_strength ::= ( strength0 , strength1 )
// -----------------------------------------------------------------------------
TEST(ParserA302, PullupStrength_Strength0Strength1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (strong0, pull1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);  // strong0
  EXPECT_EQ(g->drive_strength1, 3u);  // pull1
  EXPECT_EQ(g->gate_inst_name, "pu1");
}

}  // namespace
