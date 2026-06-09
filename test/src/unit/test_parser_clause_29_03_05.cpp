#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(UdpZValues, ZSymbolInInputFieldRejected) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    z 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpZValues, ZSymbolInOutputFieldRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : z;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpZValues, ZSymbolInCurrentStateFieldRejected) {
  auto r = Parse(
      "primitive p(output reg q, input d, input en);\n"
      "  table\n"
      "    0 1 : z : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpZValues, UppercaseZSymbolInInputFieldRejected) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    Z 0 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpZValues, ZSymbolInParenthesizedEdgeRejected) {
  auto r = Parse(
      "primitive p(output reg q, input a, input b);\n"
      "  table\n"
      "    (0z) 0 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// The z-scan flags either endpoint of a parenthesized edge; the case above
// hits the closing endpoint, this one hits the starting endpoint.
TEST(UdpZValues, ZSymbolAtStartOfParenthesizedEdgeRejected) {
  auto r = Parse(
      "primitive p(output reg q, input a, input b);\n"
      "  table\n"
      "    (z0) 0 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

}
