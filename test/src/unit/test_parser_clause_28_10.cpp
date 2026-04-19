// §28.10

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(PullSources, EmptyTerminals) {
  auto r = Parse(
      "module m;\n"
      "  pullup ();\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PullSources, PullupAndPulldownInstantiation) {
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

TEST(PullSources, PullupGateKindAndSingleTerminal) {
  auto r = ParseWithPreprocessor("module t; pullup (o); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kPullup);
  EXPECT_EQ(item->gate_terminals.size(), 1);
}

TEST(PullSources, PulldownGateKindAndSingleTerminal) {
  auto r = ParseWithPreprocessor("module t; pulldown (o); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kPulldown);
  EXPECT_EQ(item->gate_terminals.size(), 1);
}

// §28.10 explicitly forbids delay specifications on pullup/pulldown.
TEST(PullSources, PullupRejectsDelay) {
  auto r = Parse(
      "module m;\n"
      "  pullup #5 pu1(net1);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PullSources, PulldownRejectsDelay) {
  auto r = Parse(
      "module m;\n"
      "  pulldown #5 pd1(net1);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
