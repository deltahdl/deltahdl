#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(UdpEdgeSeq, SingleEdgeIndicatorInRowAccepted) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpEdgeSeq, TwoParenthesizedEdgeIndicatorsInRowRejected) {
  auto r = Parse(
      "primitive bad(output reg q, input a, input b, input c);\n"
      "  table\n"
      "    (01) (10) 0 : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row shall contain at most one input transition", 3,
      "29.3.4"));
}

TEST(UdpEdgeSeq, TwoLetterEdgeSymbolsInRowRejected) {
  auto r = Parse(
      "primitive bad(output reg q, input a, input b);\n"
      "  table\n"
      "    r f : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row shall contain at most one input transition", 3,
      "29.3.4"));
}

bool TwoTransitionRowReported(const char* row) {
  auto r = Parse(std::string("primitive bad(output reg q, input a, input b);\n"
                             "  table\n"
                             "    ") +
                 row +
                 "\n"
                 "  endtable\n"
                 "endprimitive\n");
  return ReportedError(
      r.diags, "UDP table row shall contain at most one input transition", 3,
      "29.3.4");
}

TEST(UdpEdgeSeq, ParenthesizedEdgeBesideALetterEdgeRejected) {
  EXPECT_TRUE(TwoTransitionRowReported("(01) f : ? : 0;"));
}

TEST(UdpEdgeSeq, LetterEdgeBesideAStarRejected) {
  EXPECT_TRUE(TwoTransitionRowReported("r * : ? : 0;"));
}

TEST(UdpEdgeSeq, AdjacentParenthesizedEdgesWithoutSpacesRejected) {
  auto r = Parse(
      "primitive bad(output reg q, input a, input b, input c);\n"
      "  table\n"
      "    (01)(01)0 : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row shall contain at most one input transition", 3,
      "29.3.4"));
}

TEST(UdpEdgeSeq, SingleParenthesizedEdgeBesideLevelsAccepted) {
  auto r = Parse(
      "primitive ok(output reg q, input a, input b, input c);\n"
      "  table\n"
      "    (01) 1 0 : 0 : 1;\n"
      "    0 (10) 1 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
