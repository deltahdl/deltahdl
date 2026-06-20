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

}  // namespace
