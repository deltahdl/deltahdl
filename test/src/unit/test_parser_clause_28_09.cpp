// §28.9

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(CmosSwitches, TooManyTerminals) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(out, data, nctrl, pctrl, extra);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(CmosSwitches, ThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  cmos #(10, 20, 30) c1(out, data, nctrl, pctrl);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
}

}  // namespace
