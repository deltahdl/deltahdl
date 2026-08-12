#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §30.7.1: a path-specific PATHPULSE$in$out specparam's terminals must conform
// to the module-path input/output rules of §30.4.1. Correct directions -- an
// input source terminal and an output destination terminal -- elaborate
// cleanly.
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

// §30.4.1 applied to the PATHPULSE$ input terminal: a source must be an input
// or inout port, so naming an output port as the input terminal is rejected.
// §30.7.1 states no direction rule of its own and defers -- "The module path
// input terminals and output terminals shall conform to the rules for module
// path inputs and outputs" -- so the report carries §30.4.1, where those rules
// are stated.
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
  const delta::Diagnostic* diag =
      FindDiag(f, "PATHPULSE$ input terminal 'q' must be an input");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "30.4.1");
}

// §30.4.1 applied to the PATHPULSE$ output terminal: a destination must be an
// output or inout port, so naming an input port as the output terminal is
// rejected. §30.7.1 defers here too, so the report carries §30.4.1.
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
  const delta::Diagnostic* diag =
      FindDiag(f, "PATHPULSE$ output terminal 'clk' must be an output");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "30.4.1");
}

// An inout port satisfies both the source and destination direction rules, so
// it is accepted at either terminal position.
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

// A non-path-specific PATHPULSE$ names no terminals, so the direction check
// does not apply and a wrong-direction diagnostic is never raised for it.
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
