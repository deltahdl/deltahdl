#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(PrimitiveGateTypeParsing, EnableGatetype_Bufif0) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, EnableGatetype_Bufif1) {
  auto r = Parse(
      "module m;\n"
      "  bufif1 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, EnableGatetype_Notif0) {
  auto r = Parse(
      "module m;\n"
      "  notif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, EnableGatetype_Notif1) {
  auto r = Parse(
      "module m;\n"
      "  notif1 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

}  // namespace
