#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(PrimitiveInstantiationParsing, GateInst_PulldownBasic) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(PrimitiveInstantiationParsing, GateInst_PullupBasic) {
  auto r = Parse(
      "module m;\n"
      "  pullup (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(PrimitiveInstantiationParsing, PullGateInst_PullupNamed) {
  auto r = Parse(
      "module m;\n"
      "  pullup pu1(net1);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "pu1");
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(PrimitiveInstantiationParsing, PullGateInst_PulldownNamed) {
  auto r = Parse(
      "module m;\n"
      "  pulldown pd1(net1);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "pd1");
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(PrimitiveInstantiationParsing, PullGateInst_PullupUnnamed) {
  auto r = Parse(
      "module m;\n"
      "  pullup (net1);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

TEST(PullSources, PullupAndPulldown) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire a, b;\n"
              "  pullup   g1(a);\n"
              "  pulldown g2(b);\n"
              "endmodule\n"));
}

}  // namespace
