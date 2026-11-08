#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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
