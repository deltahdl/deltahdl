// §28.10: pullup and pulldown sources

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.3.1 Production #1: gate_instantiation (pulldown alternative)
// gate_instantiation ::=
//   pulldown [pulldown_strength] pull_gate_instance {, pull_gate_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_PulldownBasic) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

// =============================================================================
// A.3.1 Production #1: gate_instantiation (pullup alternative)
// gate_instantiation ::=
//   pullup [pullup_strength] pull_gate_instance {, pull_gate_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_PullupBasic) {
  auto r = Parse(
      "module m;\n"
      "  pullup (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

// =============================================================================
// A.3.1 Production #9: pull_gate_instance
// pull_gate_instance ::= [name_of_instance] ( output_terminal )
// =============================================================================
TEST(ParserA301, PullGateInst_PullupNamed) {
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

}  // namespace
