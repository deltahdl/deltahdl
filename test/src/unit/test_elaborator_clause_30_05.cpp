#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §30.5: delay values shall be constant expressions containing literals or
// specparams; a regular net reference is not a valid delay operand.
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

// §30.5: a specparam is a valid delay operand.
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

// §30.5: a constant expression combining literals and specparams is a valid
// delay operand.
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

}  // namespace
