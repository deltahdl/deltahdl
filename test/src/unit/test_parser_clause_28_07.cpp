// §28.7

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- Terminal count error cases not covered by subsection files ---
TEST(MosSwitches, TooFewTerminals) {
  auto r = Parse(
      "module m;\n"
      "  nmos n1(out, data);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(MosSwitches, TooManyTerminals) {
  auto r = Parse(
      "module m;\n"
      "  pmos p1(out, data, ctrl, extra);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(MosSwitches, ThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  nmos #(10, 20, 30) n1(out, data, ctrl);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
}

}  // namespace
