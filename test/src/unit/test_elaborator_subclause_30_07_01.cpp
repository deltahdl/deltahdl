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
