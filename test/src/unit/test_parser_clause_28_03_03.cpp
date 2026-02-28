// §28.3.3: The delay specification

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA301, GateInst_NOutputWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  not #(4, 6) n1(out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_NE(g->gate_delay_fall, nullptr);
}

TEST(ParserA301, GateInst_SharedDelayAcrossInstances) {
  auto r = Parse(
      "module m;\n"
      "  or #5 o1(out1, a, b), o2(out2, c, d);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_NE(gates[0]->gate_delay, nullptr);
  EXPECT_NE(gates[1]->gate_delay, nullptr);
}

}  // namespace
