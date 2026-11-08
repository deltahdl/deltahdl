#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(TimingCheckLimitConstness, LiteralLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingCheckLimitConstness, SpecparamLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  specify\n"
      "    specparam tSetup = 5;\n"
      "    $setup(d, posedge clk, tSetup);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingCheckLimitConstness, SpecparamExpressionLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  specify\n"
      "    specparam tA = 2, tB = 3;\n"
      "    $setup(d, posedge clk, tA + tB);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingCheckLimitConstness, VariableLimitRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  logic [7:0] tSetup;\n"
      "  specify\n"
      "    $setup(d, posedge clk, tSetup);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check limit operand 'tSetup' is not a "
                            "specparam",
                            4, "31.2"));
}

TEST(TimingCheckLimitConstness, MixedSpecparamAndVariableLimitRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  logic [7:0] w;\n"
      "  specify\n"
      "    specparam tA = 2;\n"
      "    $setup(d, posedge clk, tA + w);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check limit operand 'w' is not a specparam",
                            5, "31.2"));
}

TEST(TimingCheckLimitConstness, ModuleParameterLimitRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  parameter P = 5;\n"
      "  specify\n"
      "    $setup(d, posedge clk, P);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check limit operand 'P' is not a specparam",
                            4, "31.2"));
}

TEST(TimingCheckLimitConstness, LocalparamLimitRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  localparam L = 5;\n"
      "  specify\n"
      "    $setup(d, posedge clk, L);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check limit operand 'L' is not a specparam",
                            4, "31.2"));
}

TEST(TimingCheckTerminals, LocalVariableDataEventRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module dut(input clk);\n"
      "  reg d = 0; reg n = 0;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5, n);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check terminal 'd' is not a port of the "
                            "module",
                            4, "31.2"));
}

TEST(TimingCheckTerminals, LocalNetReferenceEventRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module dut(input d);\n"
      "  wire c;\n"
      "  specify\n"
      "    $hold(posedge c, d, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check terminal 'c' is not a port of the "
                            "module",
                            4, "31.2"));
}

TEST(TimingCheckTerminals, PortsOfEveryDirectionAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module dut(input d, inout clk, output q);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5);\n"
      "    $hold(posedge clk, q, 2);\n"
      "    $width(negedge q, 4);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TimingCheckTerminals, InterfacePortMemberAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface bus;\n"
      "  logic d, clk;\n"
      "endinterface\n"
      "module dut(bus b);\n"
      "  specify\n"
      "    $setup(b.d, posedge b.clk, 5);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top;\n"
      "  bus i();\n"
      "  dut u(.b(i));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
