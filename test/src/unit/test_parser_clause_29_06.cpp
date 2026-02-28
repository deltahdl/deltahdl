// §29.6: Edge-sensitive sequential UDPs

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// --- Sequential UDP edge-sensitive evaluation ---
TEST(ParserAnnexA051, SimSequentialEdgeSensitive) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 1'bx;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "    ? f : ? : -;\n"
      "    * ? : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];

  UdpEvalState state(*udp);
  EXPECT_EQ(state.GetOutput(), 'x');

  state.SetInputs({'1', '0'});
  state.EvaluateWithEdge({'1', '1'}, 1, '0');
  EXPECT_EQ(state.GetOutput(), '1');

  state.EvaluateWithEdge({'1', '0'}, 1, '1');
  EXPECT_EQ(state.GetOutput(), '1');

  state.EvaluateWithEdge({'0', '0'}, 0, '1');
  EXPECT_EQ(state.GetOutput(), '1');

  state.EvaluateWithEdge({'0', '1'}, 1, '0');
  EXPECT_EQ(state.GetOutput(), '0');
}

// ---------------------------------------------------------------------------
// Production 11: edge_indicator ::= ( level_symbol level_symbol ) |
//                edge_symbol
// ---------------------------------------------------------------------------
// edge_indicator as edge_symbol
TEST(ParserAnnexA053, EdgeIndicator_EdgeSymbol) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->table[0].inputs[1], 'r');
}

}  // namespace
