#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(GateLevelModelingParsing, PullGates) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  pullup (out);\n"
      "  pulldown (out);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  EXPECT_EQ(mod->items[0]->gate_kind, GateKind::kPullup);
  EXPECT_EQ(mod->items[1]->gate_kind, GateKind::kPulldown);
}

TEST(Parser, GatePullup) {
  auto r = ParseWithPreprocessor("module t; pullup (o); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kPullup);
  EXPECT_EQ(item->gate_terminals.size(), 1);
}

TEST(PullupPulldownSources, PullupAndPulldownInstantiation) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire net1;\n"
      "  pullup (net1);\n"
      "  pulldown (net1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown),
            nullptr);
}

}  // namespace
