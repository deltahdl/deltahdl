#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// Whether `message` is reported under A.2.11 at each of `reported` and at
// none of `clean`.
void ExpectReportedAt(const ParseResult& r, const std::string& message,
                      std::initializer_list<uint32_t> reported,
                      std::initializer_list<uint32_t> clean) {
  for (uint32_t line : reported) {
    EXPECT_TRUE(ReportedError(r.diags, message, line, "A.2.11"))
        << "line " << line;
  }
  for (uint32_t line : clean) {
    EXPECT_FALSE(ReportedError(r.diags, message, line, "A.2.11"))
        << "line " << line;
  }
}

// A.2.11's covergroup_value_range admits `$` as one bound of a `:` range
// alone: not as both bounds, and not as a tolerance's center.
TEST(CovergroupItemSyntax, ADollarStandsForOneBoundOfARangeAlone) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins all = { [$:$] };\n"
      "      bins near = { [$ +/- 2] };\n"
      "      bins pct = { [$ +%- 10] };\n"
      "      bins lo = { [$:4] };\n"
      "      bins hi = { [5:$] };\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  ExpectReportedAt(
      r, "'$' stands for one bound of a '[ lo : hi ]' value range alone",
      {5, 6, 7}, {8, 9});
}

// A.2.11's list_of_cross_items puts one comma between each two items, so a
// comma before the first, after the last or beside another is reported, once
// for the list however many it holds; a cross naming nothing has no comma
// to report.
TEST(CovergroupItemSyntax, ACrossListsItsItemsWithACommaBetweenEachTwo) {
  auto r = Parse(
      "module m;\n"
      "  int a, b;\n"
      "  covergroup cg;\n"
      "    coverpoint a;\n"
      "    coverpoint b;\n"
      "    c1: cross a, b,;\n"
      "    c2: cross , a, , b;\n"
      "    c3: cross a, , b;\n"
      "    c4: cross a, b;\n"
      "    c5: cross;\n"
      "  endgroup\n"
      "endmodule\n");
  ExpectReportedAt(
      r, "a cross lists its items with one ',' between each two of them",
      {6, 7, 8}, {9, 10});
}

// A.2.11 lets a data type stand before a coverpoint's label alone; a cross
// takes none.
TEST(CovergroupItemSyntax, ACrossTakesNoDataType) {
  auto r = Parse(
      "module m;\n"
      "  int a, b;\n"
      "  covergroup cg;\n"
      "    coverpoint a;\n"
      "    coverpoint b;\n"
      "    int c1 : cross a, b;\n"
      "    bit [3:0] cp : coverpoint a;\n"
      "    c2 : cross a, b;\n"
      "  endgroup\n"
      "endmodule\n");
  ExpectReportedAt(r,
                   "a cross takes no data type; one is written before a "
                   "coverpoint's label alone",
                   {6}, {7, 8});
}

// A.2.11 leaves nothing between a complete coverpoint, cross or covergroup
// option and the ';' or body that ends it, so the first token standing there
// is reported.
TEST(CovergroupItemSyntax, ATokenAfterACompleteItemIsReported) {
  auto r = Parse(
      "module m;\n"
      "  int a, b;\n"
      "  bit en;\n"
      "  covergroup cg;\n"
      "    option.goal = 90 90;\n"
      "    coverpoint a b;\n"
      "    coverpoint b iff (en) a { }\n"
      "    cross a, b iff (en) b;\n"
      "    option.weight = 2;\n"
      "    coverpoint en iff (b) { }\n"
      "  endgroup\n"
      "endmodule\n");
  const std::string kComplete = "a covergroup item is complete here; '";
  const std::string kTail = "' is not part of it";
  ExpectReportedAt(r, kComplete + "90" + kTail, {5}, {});
  ExpectReportedAt(r, kComplete + "b" + kTail, {6, 8}, {});
  ExpectReportedAt(r, kComplete + "a" + kTail, {7}, {});
  for (uint32_t line : {9u, 10u}) {
    EXPECT_FALSE(ReportedError(r.diags, kComplete, line, "A.2.11"))
        << "line " << line;
  }
}

// The end of the file after a coverpoint is a missing terminator, which the
// covergroup's 'endgroup' report covers, not a token standing after the item.
TEST(CovergroupItemSyntax, TheEndOfTheFileIsNoTokenAfterAnItem) {
  auto r = Parse(
      "module m;\n"
      "  int a;\n"
      "  covergroup cg;\n"
      "    coverpoint a");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endgroup', got EOF", 4, "19.3"));
  EXPECT_FALSE(ReportedError(r.diags, "a covergroup item is complete here", 4,
                             "A.2.11"));
}

// A.2.11's select_expression negates a select_condition alone, so a `!`
// before a parenthesized select_expression is reported.
TEST(CovergroupItemSyntax, ANegationTakesABinsofCondition) {
  auto r = Parse(
      "module m;\n"
      "  int a, b;\n"
      "  covergroup cg;\n"
      "    coverpoint a { bins lo = {[0:3]}; }\n"
      "    coverpoint b { bins lo = {[0:3]}; }\n"
      "    c1: cross a, b {\n"
      "      bins x = ! (binsof(a) && binsof(b));\n"
      "      bins y = ! binsof(a.lo);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  ExpectReportedAt(r,
                   "'!' negates a binsof select_condition; 'binsof' follows it",
                   {7}, {8});
}

// A.2.11's select_condition names a bins_expression inside binsof's
// parentheses.
TEST(CovergroupItemSyntax, ABinsofNamesWhatItSelects) {
  auto r = Parse(
      "module m;\n"
      "  int a, b;\n"
      "  covergroup cg;\n"
      "    coverpoint a;\n"
      "    coverpoint b;\n"
      "    c1: cross a, b {\n"
      "      bins x = binsof();\n"
      "      bins y = binsof(a);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  ExpectReportedAt(r,
                   "binsof names a coverpoint, a coverpoint's bin or a "
                   "variable; none is written",
                   {7}, {8});
}

// A.2.11 names every bin, a coverpoint's and a cross's bins selection alike.
TEST(CovergroupItemSyntax, ABinIsNamed) {
  auto r = Parse(
      "module m;\n"
      "  int a, b;\n"
      "  covergroup cg;\n"
      "    coverpoint a {\n"
      "      bins = { 1 };\n"
      "      bins [] = { [0:3] };\n"
      "      bins one = { 1 };\n"
      "    }\n"
      "    coverpoint b;\n"
      "    c1: cross a, b {\n"
      "      ignore_bins = binsof(a);\n"
      "      bins pair = binsof(b);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  ExpectReportedAt(r,
                   "a bin is named; a bin_identifier follows its bins keyword",
                   {5, 6, 11}, {7, 12});
}

// A.6.5's clocking_event writes `@` and a name, a package-scoped or a
// hierarchical one whose prefixes may select, unless it parenthesizes an
// event expression; so a coverage event that is an operation or ends in a
// select is reported under A.6.5.
TEST(CovergroupItemSyntax, AnUnparenthesizedCoverageEventIsAName) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, en;\n"
      "  logic [1:0] w;\n"
      "  int x;\n"
      "  covergroup cg1 @ clk + 1;\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  covergroup cg2 @ w[0];\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  covergroup cg3 @ clk;\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  covergroup cg4 @ m.u[0].clk;\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  covergroup cg5 @ (posedge clk iff en);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n");
  const char* const kMessage =
      "an unparenthesized clocking event is '@' and a name; an expression is "
      "parenthesized";
  for (uint32_t line : {5u, 8u}) {
    EXPECT_TRUE(ReportedError(r.diags, kMessage, line, "A.6.5"))
        << "line " << line;
  }
  for (uint32_t line : {11u, 14u, 17u}) {
    EXPECT_FALSE(ReportedError(r.diags, kMessage, line, "A.6.5"))
        << "line " << line;
  }
}

}  // namespace
