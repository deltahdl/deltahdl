// Annex A.5.2: UDP ports

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// ANSI port list with mixed input keyword usage
// (some inputs have 'input' keyword, some share the previous one)
TEST(ParserAnnexA052, AnsiPortList_MixedInputKeyword) {
  auto r = Parse(
      "primitive gate(output out, input a, input b, c);\n"
      "  table\n"
      "    0 0 0 : 0;\n"
      "    1 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 3u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_EQ(udp->input_names[2], "c");
}

}  // namespace
