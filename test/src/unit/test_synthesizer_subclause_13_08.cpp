#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// A call to a static method of a parameterized class reaches
// SynthLower::LowerExprBit as ExprKind::kCall, and the synthesizer has no
// lowering for it, so it reports the call under §13.4 and SynthLower::Lower
// answers with nothing. The case used to assert only that a graph came back,
// which held while kCall fell through to constant zero: `q` came out zero
// rather than following `d`, and nothing said so.
//
// The name this case carried, StaticFunctionCallSynthesizes, claimed a netlist
// in which `q` tracks `d` through C#(8)::identity. To claim that again the
// lowering would have to bind each actual argument to the formal of the
// specialization named, lower the body of that function under the binding, and
// drive the assignment target from the value `return` leaves; until it does,
// the refusal is what is true.
TEST(ParameterizedSubroutineSynthesis, StaticFunctionCallIsReportedUnlowered) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "virtual class C#(parameter W = 8);\n"
                   "  static function logic [W-1:0] identity(\n"
                   "      input logic [W-1:0] x);\n"
                   "    return x;\n"
                   "  endfunction\n"
                   "endclass\n"
                   "module m(input logic [7:0] d, output logic [7:0] q);\n"
                   "  assign q = C#(8)::identity(d);\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a function call has no lowering in the "
                            "synthesizer",
                            8, "13.4"));
}

// Two calls to the same static method through different specializations are two
// ExprKind::kCall nodes, so each draws its own §13.4 report at the line it is
// written on rather than one report standing for both. The case used to assert
// only that a graph came back, which held while both calls fell through to
// constant zero and neither `x` nor `y` followed its input.
TEST(ParameterizedSubroutineSynthesis,
     BothSpecializationCallsAreReportedUnlowered) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "virtual class C#(parameter W = 8);\n"
                   "  static function logic [W-1:0] identity(\n"
                   "      input logic [W-1:0] x);\n"
                   "    return x;\n"
                   "  endfunction\n"
                   "endclass\n"
                   "module m(input logic [3:0] a, input logic [7:0] b,\n"
                   "         output logic [3:0] x, output logic [7:0] y);\n"
                   "  assign x = C#(4)::identity(a);\n"
                   "  assign y = C#(8)::identity(b);\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a function call has no lowering in the "
                            "synthesizer",
                            9, "13.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a function call has no lowering in the "
                            "synthesizer",
                            10, "13.4"));
}

}  // namespace
