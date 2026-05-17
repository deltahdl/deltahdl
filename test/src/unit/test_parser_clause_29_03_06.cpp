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

TEST(UdpSymbols, MinusInSequentialCurrentStateRejected) {
  auto r = Parse(
      "primitive p(output reg q, input d, input en);\n"
      "  table\n"
      "    0 1 : - : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpSymbols, MinusInInputFieldRejected) {
  auto r = Parse(
      "primitive p(output reg q, input a, input b);\n"
      "  table\n"
      "    - 0 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpSymbols, EdgeSymbolInOutputFieldRejected) {
  auto r = Parse(
      "primitive p(output reg q, input a);\n"
      "  table\n"
      "    0 : ? : r;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpSymbols, EdgeSymbolInCurrentStateFieldRejected) {
  auto r = Parse(
      "primitive p(output reg q, input a);\n"
      "  table\n"
      "    0 : r : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpSymbols, ParenthesizedEdgeWithInvalidSymbolRejected) {
  auto r = Parse(
      "primitive p(output reg q, input a);\n"
      "  table\n"
      "    (0r) : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

}
