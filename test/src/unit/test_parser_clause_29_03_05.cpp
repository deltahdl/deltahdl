#include "fixture_parser.h"

using namespace delta;

namespace {

// The z state is not a permitted symbol anywhere in a UDP state table; placing
// it in an input field is rejected.
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

// The z state is not permitted in the output field.
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

// The z state is not permitted in the current-state field of a sequential UDP.
TEST(UdpZValues, ZSymbolInCurrentStateFieldRejected) {
  auto r = Parse(
      "primitive p(output reg q, input d, input en);\n"
      "  table\n"
      "    0 1 : z : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// The uppercase Z spelling is treated the same as the lowercase z form and
// is likewise illegal in a table entry.
TEST(UdpZValues, UppercaseZSymbolInInputFieldRejected) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    Z 0 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// A z appearing inside a parenthesized edge indicator is part of the table
// entry and is illegal just like a bare-level z.
TEST(UdpZValues, ZSymbolInParenthesizedEdgeRejected) {
  auto r = Parse(
      "primitive p(output reg q, input a, input b);\n"
      "  table\n"
      "    (0z) 0 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
