#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// A system function call on the right of a continuous assignment reaches
// SynthLower::LowerExprBit as ExprKind::kSystemCall, and the synthesizer has no
// lowering for it, so it reports the call under §5.6.3 and SynthLower::Lower
// answers with nothing. The case used to assert only that a graph came back,
// which held while kSystemCall fell through to constant zero: the netlist then
// drove `w` to zero rather than to $clog2(16), and nothing said so.
TEST(SystemNameSynthesis, SystemFunctionInAssignIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [31:0] w;\n"
                           "  assign w = $clog2(16);\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a system task or system function has no lowering in the synthesizer", 3,
      "5.6.3"));
}

// The same ExprKind::kSystemCall report under §5.6.3 when the call is one
// operand of a §11.4.3 addition rather than the whole right-hand side, so the
// operand a lowered adder cannot supply is named where it is written. The case
// used to assert only that a graph came back, which held while the call
// contributed constant zero to every bit of that sum.
TEST(SystemNameSynthesis, SystemFunctionInAdditionIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] a, result;\n"
                           "  assign result = a + $clog2(32);\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a system task or system function has no lowering in the synthesizer", 3,
      "5.6.3"));
}

// $bits, whose argument is a data type rather than an expression, is
// ExprKind::kSystemCall like any other system function and is reported under
// §5.6.3 alike. The case used to assert only that a graph came back, which held
// while the call contributed constant zero to `w`.
TEST(SystemNameSynthesis, SystemFunctionWithDataTypeArgIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [31:0] w;\n"
                           "  assign w = $bits(logic [7:0]);\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a system task or system function has no lowering in the synthesizer", 3,
      "5.6.3"));
}

// §5.6.3: a system construct is not design semantics but refers to simulator
// functionality, so it has no hardware to become. The report names the callee
// and stands at the `$`, so a design calling several says which one and where.
TEST(SystemNameSynthesis, SystemCallIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic x;\n"
                           "  always_comb begin\n"
                           "    x = 1'b0;\n"
                           "    $exit();\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "system task or system function '$exit' is not synthesizable", 5,
      "5.6.3"));
}

}  // namespace
