#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// This file covers the function call §13.4 defines, written on the right-hand
// side of a continuous assignment, which `SynthLower::LowerExprBit` in
// src/synthesizer/synth_lower.cpp has no lowering for.

// The case fails on a run that answers a netlist for this module. The
// right-hand side reaches `SynthLower::LowerExprBit` in
// src/synthesizer/synth_lower.cpp as an `ExprKind::kCall`, and that function
// builds no node for the kind. A design that wrote the call got a netlist
// contributing constant zero at every bit of the expression while the run
// reported success. §13.4 rules that a function returns a value to be used in
// an expression, and the value returned here is the eight bits the target
// declares.
TEST(FunctionCallSynthesis, FunctionCallIsReportedRatherThanLoweredToZero) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [7:0] d, output logic [7:0] q);\n"
                   "  function logic [7:0] identity(input logic [7:0] v);\n"
                   "    return v;\n"
                   "  endfunction\n"
                   "  assign q = identity(d);\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a function call has no lowering", 5, "13.4"));
}

}  // namespace
