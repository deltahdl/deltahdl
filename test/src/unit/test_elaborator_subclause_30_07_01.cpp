#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PulseControlTerminalElaboration, CorrectDirectionTerminalsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    specparam PATHPULSE$clk$q = (1, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PulseControlTerminalElaboration, InputTerminalMayNotBeOutputPort) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    specparam PATHPULSE$q$q = (1, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "PATHPULSE$ input terminal 'q' must be an input", 3,
                            "30.4.1"));
}

TEST(PulseControlTerminalElaboration, OutputTerminalMayNotBeInputPort) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    specparam PATHPULSE$clk$clk = (1, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "PATHPULSE$ output terminal 'clk' must be an output", 3, "30.4.1"));
}

TEST(PulseControlTerminalElaboration, InoutTerminalsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(inout io, input clk, output q);\n"
      "  specify\n"
      "    specparam PATHPULSE$io$io = (2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PulseControlTerminalElaboration,
     DISABLED_InputTerminalMayNotBeInternalNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, output q);\n"
      "  wire w;\n"
      "  specify\n"
      "    specparam PATHPULSE$w$q = (1, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "PATHPULSE$ input terminal 'w' must be an input or inout port", 4,
      "30.4.1"));
}

TEST(PulseControlTerminalElaboration,
     DISABLED_OutputTerminalMayNotBeInternalNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, output q);\n"
      "  wire w;\n"
      "  specify\n"
      "    specparam PATHPULSE$clk$w = (1, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "PATHPULSE$ output terminal 'w' must be an output or inout port", 4,
      "30.4.1"));
}

TEST(PulseControlTerminalElaboration, DISABLED_TerminalMayNotBeUndeclaredName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    specparam PATHPULSE$zz$q = (1, 3);\n"
      "    specparam PATHPULSE$clk$zz = (1, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "PATHPULSE$ input terminal 'zz' must be an input or inout port", 3,
      "30.4.1"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "PATHPULSE$ output terminal 'zz' must be an output or inout port", 4,
      "30.4.1"));
}

TEST(PulseControlTerminalElaboration,
     DISABLED_ModuleLevelTerminalDirectionsAreChecked) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, output q);\n"
      "  specparam PATHPULSE$q$q = (1, 3);\n"
      "  specparam PATHPULSE$clk$clk = (1, 3);\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "PATHPULSE$ input terminal 'q' must be an input or inout port", 2,
      "30.4.1"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "PATHPULSE$ output terminal 'clk' must be an output or inout port", 3,
      "30.4.1"));
}

TEST(PulseControlTerminalElaboration, ModuleLevelPortTerminalsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, inout io, output q);\n"
      "  specparam PATHPULSE$clk$q = (1, 3);\n"
      "  specparam PATHPULSE$io$io = (2);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PulseControlLimitElaboration, NonConstantLimitIsReported) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    specparam PATHPULSE$ = (a);\n"
      "    specparam PATHPULSE$b$y = (1, a);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "specparam 'PATHPULSE$' value is not a constant expression",
                    3, "6.20.2"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "specparam 'PATHPULSE$b$y' value is not a constant expression", 4,
      "6.20.2"));
}

TEST(PulseControlLimitElaboration, ModuleLevelNonConstantLimitIsReported) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  specparam PATHPULSE$ = (a);\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "specparam 'PATHPULSE$' value is not a constant expression",
                    2, "6.20.2"));
}

TEST(PulseControlLimitElaboration, ConstantLimitOperandsAreAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  parameter P = 2;\n"
      "  localparam L = 3;\n"
      "  specparam S = 4;\n"
      "  specify\n"
      "    specparam PATHPULSE$ = (P, L + S);\n"
      "    specparam PATHPULSE$a$y = (1:P:3, S);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PulseControlTerminalElaboration, NonPathSpecificSkipsTerminalCheck) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    specparam PATHPULSE$ = (2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
