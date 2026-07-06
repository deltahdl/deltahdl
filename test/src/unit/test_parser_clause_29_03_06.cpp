// §29.3.6 "Summary of symbols" (Table 29-1) defines, for every UDP table
// symbol, which fields of a row it may legally occupy. These parser-stage tests
// drive real UDP source through the pipeline and observe the field-permission
// diagnostics emitted from parser_udp.cpp:
//   - ?  and b : permitted in input (and sequential current-state) fields, but
//                not in the output field.
//   - -        : permitted only in the output field of a sequential UDP.
//   - edges /
//     (vw)     : only permitted in the input field.
//   - x        : permitted in the input, output, and current-state fields.
//
// The complementary symbol-matching semantics live in the simulator canonical
// file for this subclause.
#include "fixture_parser.h"

using namespace delta;

namespace {

// ? and b iterate over level values but are barred from the output field.

TEST(UdpSymbolFields, QuestionInOutputFieldRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : ?;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpSymbolFields, BInOutputFieldRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : b;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpSymbolFields, QuestionInInputFieldAccepted) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    ? 0 : 1;\n"
      "    ? 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpSymbolFields, BInInputFieldAccepted) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    b 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ? and b are also permitted in the current-state field of a sequential UDP.

TEST(UdpSymbolFields, QuestionInSequentialCurrentStateAccepted) {
  auto r = Parse(
      "primitive p(output reg q, input a, input b);\n"
      "  table\n"
      "    0 0 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpSymbolFields, BInSequentialCurrentStateAccepted) {
  auto r = Parse(
      "primitive p(output reg q, input a, input b);\n"
      "  table\n"
      "    0 0 : b : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// - means "no change" and is permitted only in the output field of a
// sequential UDP.

TEST(UdpSymbolFields, DashInInputFieldRejected) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    - 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpSymbolFields, DashInCombinationalOutputRejected) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    0 1 : -;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpSymbolFields, DashInSequentialCurrentStateRejected) {
  auto r = Parse(
      "primitive p(output reg q, input a, input b);\n"
      "  table\n"
      "    0 0 : - : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpSymbolFields, DashInSequentialOutputAccepted) {
  auto r = Parse(
      "primitive p(output reg q, input a, input b);\n"
      "  table\n"
      "    0 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Edge and (vw) transition symbols are only permitted in the input field; an
// edge symbol in the current-state field is rejected.

TEST(UdpSymbolFields, EdgeSymbolInCurrentStateRejected) {
  auto r = Parse(
      "primitive p(output reg q, input a, input b);\n"
      "  table\n"
      "    0 0 : r : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// The accepting side: a (vw) transition symbol in an input field is permitted.
TEST(UdpSymbolFields, TransitionSymbolInInputFieldAccepted) {
  auto r = Parse(
      "primitive p(output reg q, input clk, input d);\n"
      "  table\n"
      "    (01) 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// x is permitted in the input, output, and current-state fields.

TEST(UdpSymbolFields, XInInputFieldAccepted) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    x 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpSymbolFields, XInOutputFieldAccepted) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    1 0 : x;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpSymbolFields, XInSequentialCurrentStateAccepted) {
  auto r = Parse(
      "primitive p(output reg q, input a, input b);\n"
      "  table\n"
      "    0 0 : x : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
