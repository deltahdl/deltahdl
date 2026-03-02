// §28.10: pullup and pulldown sources

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection28, PullGates) {
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

}  // namespace
