// §28.9: CMOS switches

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.3.1 Production #1: gate_instantiation (cmos_switchtype alternative)
// gate_instantiation ::=
//   cmos_switchtype [delay3] cmos_switch_instance {, cmos_switch_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_CmosBasic) {
  auto r = Parse(
      "module m;\n"
      "  cmos (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA301, GateInst_RcmosBasic) {
  auto r = Parse(
      "module m;\n"
      "  rcmos (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA301, GateInst_CmosWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  cmos #5 (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
}

TEST(ParserA301, GateInst_CmosWithDelay3) {
  auto r = Parse(
      "module m;\n"
      "  cmos #(2, 3, 4) (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_NE(g->gate_delay_fall, nullptr);
  EXPECT_NE(g->gate_delay_decay, nullptr);
}

}  // namespace
