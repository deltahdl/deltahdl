// Non-LRM tests

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// next_state as '-' (no change)
TEST(ParserAnnexA053, NextState_Dash) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].output, '-');
}

}  // namespace
