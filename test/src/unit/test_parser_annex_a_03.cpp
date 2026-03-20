// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(PrimitiveInstantiationParsing, CmosSwitchAcceptsThreeValueDelay) {
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

TEST(PrimitiveInstantiationParsing, MosSwitchAcceptsThreeValueDelay) {
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

TEST(PrimitiveInstantiationParsing, PassEnSwitchAcceptsTwoValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 #(10, 20) t1(a, b, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
}

// --- Net lvalue validation on output/inout terminals ---
TEST(PrimitiveTerminalParsing, Error_PassSwitchInoutTerminalLiteral) {
  auto r = Parse(
      "module m;\n"
      "  tran (1, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveTerminalParsing, Error_PassEnSwitchInoutTerminalExpr) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (a + b, c, en);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
