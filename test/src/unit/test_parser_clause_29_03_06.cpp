#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

TEST(UdpDeclGrammar, TableEdgeSymbols) {
  auto r = Parse(
      "primitive edge_det(output reg q, input d, input clk);\n"
      "  table\n"
      "    ? f : ? : 1;\n"
      "    ? p : ? : 0;\n"
      "    * ? : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 3u);
  EXPECT_EQ(udp->table[0].inputs[1], 'f');
  EXPECT_EQ(udp->table[1].inputs[1], 'p');
  EXPECT_EQ(udp->table[2].inputs[0], '*');
  EXPECT_EQ(udp->table[2].output, '-');
}

TEST(UdpDeclGrammar, TableWildcardSymbols) {
  auto r = Parse(
      "primitive wild(output out, input a, input b);\n"
      "  table\n"
      "    ? ? : 0;\n"
      "    b b : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 2u);
  EXPECT_EQ(udp->table[0].inputs[0], '?');
  EXPECT_EQ(udp->table[0].inputs[1], '?');
  EXPECT_EQ(udp->table[1].inputs[0], 'b');
  EXPECT_EQ(udp->table[1].inputs[1], 'b');
}

TEST(UdpDeclGrammar, SimCombinationalWildcard) {
  auto r = Parse(
      "primitive mux(output out, input a, b, sel);\n"
      "  table\n"
      "    0 ? 0 : 0;\n"
      "    1 ? 0 : 1;\n"
      "    ? 0 1 : 0;\n"
      "    ? 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];

  UdpEvalState state(*udp);
  EXPECT_EQ(state.Evaluate({'0', '1', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '0', '0'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '0', '1'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '1', '1'}), '1');
}

}  // namespace
