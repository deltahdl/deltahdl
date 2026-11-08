#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(UdpInitialStatement, CapturesInitialValueX) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 1'bx;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, 'x');
}

TEST(UdpInitialStatement, AcceptsBareSingleBitLiteral) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
}

TEST(UdpInitialStatement, AcceptsSizedOneLiteral) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 1'b1;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '1');
}

TEST(UdpInitialStatement, AcceptsSizedZeroLiteral) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 1'b0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
}

TEST(UdpInitialStatement, AcceptsBareOneLiteral) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 1;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '1');
}

TEST(UdpInitialStatement, RejectsInitialAssignmentToNonOutputPort) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial d = 1'b0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP initial statement shall target the output port", 2,
      "29.3.3"));
}

TEST(UdpInitialStatement, RejectsBlockStatementInInitial) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial begin q = 1'b0; end\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP initial statement shall be a single procedural assignment",
      2, "29.3.3"));
}

TEST(UdpInitialStatement, RejectsDelayBeforeAssignment) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial #5 q = 1'b1;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP initial statement shall not contain delay control", 2,
      "29.7"));
}

TEST(UdpInitialStatement, RejectsMultiBitSizedLiteralRhs) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 2'b10;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "UDP initial statement RHS shall be 0, 1, or a single-bit literal", 2,
      "29.3.3"));
}

}  // namespace
