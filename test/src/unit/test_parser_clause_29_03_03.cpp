#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

TEST(UdpDeclGrammar, SimSequentialWithInitial) {
  auto r = Parse(
      "primitive latch(output reg q, input d, input en);\n"
      "  initial q = 1'b0;\n"
      "  table\n"
      "    ? 0 : ? : -;\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];

  UdpEvalState state(*udp);
  EXPECT_EQ(state.GetOutput(), '0');

  state.Evaluate({'1', '1'});
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0', '0'});
  EXPECT_EQ(state.GetOutput(), '1');

  state.Evaluate({'0', '1'});
  EXPECT_EQ(state.GetOutput(), '0');
}

}  // namespace
