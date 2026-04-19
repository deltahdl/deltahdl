#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

TEST(UdpSymbols, CombinationalQuestionMarkWildcard) {
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

// ? is an iteration of 0/1/x and may not stand in for an output state.
TEST(UdpSymbols, QuestionMarkInOutputFieldRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : ?;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// b is an iteration of 0/1 and may not stand in for an output state.
TEST(UdpSymbols, BSymbolInOutputFieldRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : b;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// - means "no change" and is only meaningful as the next-state field of a
// sequential UDP; a combinational UDP has no prior output to hold.
TEST(UdpSymbols, MinusInCombinationalOutputRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : -;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// - is confined to the output field, so it is not legal in the current-state
// field of a sequential row.
TEST(UdpSymbols, MinusInSequentialCurrentStateRejected) {
  auto r = Parse(
      "primitive p(output reg q, input d, input en);\n"
      "  table\n"
      "    0 1 : - : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// - is confined to the output field, so it is not legal as an input symbol.
TEST(UdpSymbols, MinusInInputFieldRejected) {
  auto r = Parse(
      "primitive p(output reg q, input a, input b);\n"
      "  table\n"
      "    - 0 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// Edge symbols describe transitions on inputs and are not next-state values;
// placing r (or any edge) in the output field is rejected.
TEST(UdpSymbols, EdgeSymbolInOutputFieldRejected) {
  auto r = Parse(
      "primitive p(output reg q, input a);\n"
      "  table\n"
      "    0 : ? : r;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// The current-state field holds a level, not a transition, so edge symbols
// are not permitted there either.
TEST(UdpSymbols, EdgeSymbolInCurrentStateFieldRejected) {
  auto r = Parse(
      "primitive p(output reg q, input a);\n"
      "  table\n"
      "    0 : r : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// Inside a (vw) edge, both endpoints must be level symbols drawn from
// {0, 1, x, ?, b}; r is not a level symbol.
TEST(UdpSymbols, ParenthesizedEdgeWithInvalidSymbolRejected) {
  auto r = Parse(
      "primitive p(output reg q, input a);\n"
      "  table\n"
      "    (0r) : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
