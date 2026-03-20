#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

TEST(UdpDeclGrammar, SimCombinationalEval) {
  auto r = Parse(
      "primitive and_gate(output out, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 0;\n"
      "    1 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];

  UdpEvalState state(*udp);
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'0', '1'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '1'}), '1');
}

}  // namespace
