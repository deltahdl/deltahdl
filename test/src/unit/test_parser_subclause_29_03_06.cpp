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
#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP output field shall be 0, 1, or x (- is sequential only)", 3,
      "29.3.6"));
}

TEST(UdpSymbolFields, BInOutputFieldRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : b;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP output field shall be 0, 1, or x (- is sequential only)", 3,
      "29.3.6"));
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
  EXPECT_TRUE(ReportedError(r.diags, "- shall not appear in a UDP input field",
                            3, "29.3.6"));
}

TEST(UdpSymbolFields, DashInCombinationalOutputRejected) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    0 1 : -;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP output field shall be 0, 1, or x (- is sequential only)", 3,
      "29.3.6"));
}

TEST(UdpSymbolFields, DashInSequentialCurrentStateRejected) {
  auto r = Parse(
      "primitive p(output reg q, input a, input b);\n"
      "  table\n"
      "    0 0 : - : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "- shall not appear in the current-state field", 3, "29.3.6"));
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
  EXPECT_TRUE(ReportedError(
      r.diags, "edge symbols shall not appear in the current-state field", 3,
      "29.3.6"));
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

// §29.3 Syntax 29-1 writes a parenthesised edge as two level symbols. Taken
// from one token, `(011)` was read as its first two symbols. Taken from two,
// `(0x1)`, whose `x1` is one identifier, was read as `(0x)`.
TEST(UdpSymbolFields, ParenthesisedEdgeOfThreeSymbolsRejected) {
  auto r = Parse(
      "primitive p(output reg q, input clk, input d);\n"
      "  table\n"
      "    (011) 0 : ? : 0;\n"
      "    (0x1) 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "an edge in parentheses is two level symbols", 3, "29.3"));
  EXPECT_TRUE(ReportedError(
      r.diags, "an edge in parentheses is two level symbols", 4, "29.3"));
}

// The lexer hands an edge's two symbols over as one token or as two, as
// `(x1)` and `(? 0)` here do, and either way the edge has its two.
TEST(UdpSymbolFields, ParenthesisedEdgeInOneTokenOrTwoAccepted) {
  auto r = Parse(
      "primitive p(output reg q, input clk, input d);\n"
      "  table\n"
      "    (x1) 0 : ? : 0;\n"
      "    (? 0) 1 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& rows = r.cu->udps[0]->table;
  ASSERT_EQ(rows.size(), 2u);
  EXPECT_EQ(rows[0].paren_edges[0].first, 'x');
  EXPECT_EQ(rows[0].paren_edges[0].second, '1');
  EXPECT_EQ(rows[1].paren_edges[0].first, '?');
  EXPECT_EQ(rows[1].paren_edges[0].second, '0');
}

// §29.3 Syntax 29-1 makes the current-state field a level symbol, and Table
// 29-1 lists those. Only - and the edge symbols were refused there, so a digit
// other than 0 and 1, or a letter, passed as a state.
TEST(UdpSymbolFields, CurrentStateThatIsNoLevelSymbolRejected) {
  auto r = Parse(
      "primitive p(output reg q, input clk, input d);\n"
      "  table\n"
      "    r 0 : 2 : 0;\n"
      "    r 1 : q : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "the current-state field holds a level symbol (0, 1, x, X, ?, b, B)", 3,
      "29.3.6"));
  EXPECT_TRUE(ReportedError(
      r.diags,
      "the current-state field holds a level symbol (0, 1, x, X, ?, b, B)", 4,
      "29.3.6"));
}

}  // namespace
