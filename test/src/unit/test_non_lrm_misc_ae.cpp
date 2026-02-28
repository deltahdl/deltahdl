// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.3.4 Production #6: pass_en_switchtype ::= tranif0 | tranif1 | rtranif1 |
// rtranif0
// =============================================================================
TEST(ParserA304, PassEnSwitchtype_Tranif0) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (a, b, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, PassEnSwitchtype_Tranif1) {
  auto r = Parse(
      "module m;\n"
      "  tranif1 (a, b, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, PassEnSwitchtype_Rtranif0) {
  auto r = Parse(
      "module m;\n"
      "  rtranif0 (a, b, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, PassEnSwitchtype_Rtranif1) {
  auto r = Parse(
      "module m;\n"
      "  rtranif1 (a, b, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

// =============================================================================
// A.3.4 Production #7: pass_switchtype ::= tran | rtran
// =============================================================================
TEST(ParserA304, PassSwitchtype_Tran) {
  auto r = Parse(
      "module m;\n"
      "  tran (a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA304, PassSwitchtype_Rtran) {
  auto r = Parse(
      "module m;\n"
      "  rtran (a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

}  // namespace
