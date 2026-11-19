#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(UdpOutputValues, UppercaseXInAnOutputFieldIsAccepted) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : X;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpOutputValues, UppercaseZInAnOutputFieldIsRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : Z;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "UDP table row shall not contain z", 3, "29.3.5"));
}

TEST(UdpOutputValues, XInANextStateFieldIsAccepted) {
  auto r = Parse(
      "primitive p(output reg q, input d);\n"
      "  table\n"
      "    0 : ? : x;\n"
      "    1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpOutputValues, ZInANextStateFieldIsRejected) {
  auto r = Parse(
      "primitive p(output reg q, input d);\n"
      "  table\n"
      "    0 : ? : z;\n"
      "    1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "UDP table row shall not contain z", 3, "29.3.5"));
}

TEST(UdpOutputValues, AHighImpedanceInitialStatementIsRejected) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 1'bz;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "UDP initial statement RHS shall be 0, 1, or a single-bit literal", 2,
      "29.3.3"));
}

TEST(UdpOutputValues, AnUnknownAnsiHeaderInitializerIsAccepted) {
  auto r = Parse(
      "primitive dff(output reg q = 1'bx, input d, input clk);\n"
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

TEST(UdpOutputValues, DISABLED_AHighImpedanceAnsiHeaderInitializerIsRejected) {
  auto r = Parse(
      "primitive dff(output reg q = 1'bz, input d, input clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "UDP initial statement RHS shall be 0, 1, or a single-bit literal", 1,
      "29.3.3"));
}

}  // namespace
