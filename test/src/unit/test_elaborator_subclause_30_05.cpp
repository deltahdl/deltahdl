#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module path delay operand 'w' is not a specparam",
                            5, "30.5"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module path delay operand 'P' is not a specparam",
                            4, "30.5"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module path delay operand 'w' is not a specparam",
                            6, "30.5"));
}

}  // namespace
