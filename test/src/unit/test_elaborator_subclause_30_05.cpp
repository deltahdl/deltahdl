#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SpecifyPathDelayElaboration, RejectsNonSpecparamIdentifier) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [31:0] w;\n"
      "  assign w = 5;\n"
      "  specify\n"
      "    (a => b) = w;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SpecifyPathDelayElaboration, AcceptsSpecparamIdentifier) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tPD = 5;\n"
      "    (a => b) = tPD;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyPathDelayElaboration, AcceptsLiteralPlusSpecparamExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRise = 3;\n"
      "    (a => b) = tRise + 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.5: a path delay value shall be a constant expression containing literals
// or specparams.  A module parameter is a constant expression under 11.2.1, but
// it is neither a literal nor a specparam, so it is the closest constant form
// the rule must still reject -- the restriction is narrower than "any
// constant."
TEST(SpecifyPathDelayElaboration, RejectsModuleParameterOperand) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter P = 5;\n"
      "  specify\n"
      "    (a => b) = P;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §30.5: a bare literal is the simplest admitted delay-value form; observe that
// it survives elaboration's constant-operand check without error.  (The other
// accept tests exercise the specparam operand path; this one pins the literal
// path in isolation.)
TEST(SpecifyPathDelayElaboration, AcceptsLiteralValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.5: a path_delay_expression is a constant_mintypmax_expression, so a delay
// value may be min:typ:max with each component a specparam (11.11 supplies the
// mintypmax form, 6.20.5 the specparams).  Built from real source syntax and
// driven through elaboration to observe the operand check recurse into every
// mintypmax component and accept it.
TEST(SpecifyPathDelayElaboration, AcceptsMinTypMaxDelayFromSpecparams) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tmin = 1, ttyp = 2, tmax = 3;\n"
      "    (a => b) = tmin:ttyp:tmax;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.5 negative form of the mintypmax path: a non-specparam operand buried in
// a min:typ:max delay value must still be rejected, proving the
// constant-operand check descends into each mintypmax component rather than
// only the outer node.
TEST(SpecifyPathDelayElaboration, RejectsMinTypMaxWithNonSpecparamOperand) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [31:0] w;\n"
      "  assign w = 2;\n"
      "  specify\n"
      "    specparam tmin = 1, tmax = 3;\n"
      "    (a => b) = tmin:w:tmax;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
