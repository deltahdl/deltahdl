#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(UdpSequentialInitial, InitialKeywordIntroducesAssignment) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 1'b1;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '1');
}

TEST(UdpSequentialInitial, BareZeroAndOneAreSingleBitLiterals) {
  auto r0 = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r0.cu, nullptr);
  EXPECT_FALSE(r0.has_errors);
  EXPECT_EQ(r0.cu->udps[0]->initial_value, '0');

  auto r1 = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 1;\n"
      "  table\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r1.cu, nullptr);
  EXPECT_FALSE(r1.has_errors);
  EXPECT_EQ(r1.cu->udps[0]->initial_value, '1');
}

TEST(UdpSequentialInitial, UnknownSingleBitLiteralIsAccepted) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 1'bx;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->has_initial);
  EXPECT_EQ(r.cu->udps[0]->initial_value, 'x');
}

TEST(UdpSequentialInitial, CapitalBaseAndDigitSingleBitLiteral) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 1'B1;\n"
      "  table\n"
      "    0 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '1');
}

TEST(UdpSequentialInitial, SizedZeroSingleBitLiteral) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 1'b0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '0');
}

TEST(UdpSequentialInitial, UpperCaseUnknownDigitFoldsToX) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 1'bX;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->initial_value, 'x');
}

TEST(UdpSequentialInitial, NonLiteralValueIsRejected) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = seed;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "UDP initial statement RHS shall be 0, 1, or a single-bit literal", 2,
      "29.3.3"));
}

TEST(UdpSequentialInitial, AssignmentMustTargetOutputPort) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial d = 1'b0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP initial statement shall target the output port", 2,
      "29.3.3"));
}

TEST(UdpSequentialInitial, MultiBitLiteralIsRejected) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 2'b10;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "UDP initial statement RHS shall be 0, 1, or a single-bit literal", 2,
      "29.3.3"));
}

TEST(UdpSequentialInitial, BlockStatementIsRejected) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial begin q = 1'b0; end\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP initial statement shall be a single procedural assignment",
      2, "29.3.3"));
}

TEST(UdpSequentialInitial, ExpressionOpeningWithALiteralIsRejected) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 1'b1 + 1'b0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "UDP initial statement RHS shall be 0, 1, or a single-bit literal", 2,
      "29.3.3"));
}

}  // namespace
