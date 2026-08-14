#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// This file covers the tagged union expression §11.9 defines, written on the
// right-hand side of a continuous assignment, which
// `SynthLower::LowerExprBit` in src/synthesizer/synth_lower.cpp has no
// lowering for.

// The case fails on a run that answers a netlist for this module. The
// right-hand side reaches `SynthLower::LowerExprBit` in
// src/synthesizer/synth_lower.cpp as an `ExprKind::kTagged`, and that function
// builds no node for the kind. A design that wrote the expression got a
// netlist contributing constant zero at every bit of the expression while the
// run reported success. §11.9 rules that the type of a tagged union expression
// is known from its context, which the target's declared type supplies here,
// and §7.3.2 packs that type into the 33 bits of one tag bit and the widest
// member.
TEST(TaggedUnionSynthesis,
     TaggedUnionExpressionIsReportedRatherThanLoweredToZero) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(
      f,
      "module m(input [31:0] a);\n"
      "  typedef union tagged packed { void Invalid; logic [31:0] Valid; } "
      "vint_t;\n"
      "  vint_t u;\n"
      "  assign u = tagged Valid a;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a tagged union expression has no lowering", 4,
                            "11.9"));
}

}  // namespace
