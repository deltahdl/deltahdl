// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// -----------------------------------------------------------------------------
// Production #1: pulldown_strength
// pulldown_strength ::= ( strength0 )
// -----------------------------------------------------------------------------
TEST(ParserA302, PulldownStrength_SingleStrength0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (strong0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);  // strong0
  EXPECT_EQ(g->drive_strength1, 0u);  // none
}

TEST(ParserA302, PulldownStrength_SingleSupply0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (supply0) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 5u);  // supply0
  EXPECT_EQ(g->drive_strength1, 0u);  // none
}

}  // namespace
