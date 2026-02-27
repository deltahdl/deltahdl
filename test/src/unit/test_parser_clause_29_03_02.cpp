// §29.3.2: UDP port declarations

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA23, ListOfUdpPortIdentifiersMultiple) {
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
}

}  // namespace
