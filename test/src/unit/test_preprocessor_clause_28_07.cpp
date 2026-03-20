#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(GateLevelModelingParsing, MosSwitchNmos) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  nmos n1(out, data, control);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kNmos);
  EXPECT_EQ(item->gate_inst_name, "n1");
  ASSERT_EQ(item->gate_terminals.size(), 3);
}

TEST(Parser, GateNmos) {
  auto r = ParseWithPreprocessor("module t; nmos (out, in, ctrl); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kNmos);
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

TEST(MosSwitches, NmosInstantiation) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire out, data, ctrl;\n"
      "  nmos n1(out, data, ctrl);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
}

}  // namespace
