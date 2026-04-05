#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaboration, EmptyStringLiteralElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit [7:0] v;\n"
      "  initial v = \"\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elaboration, EmptyStringVsZeroCompareElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic result;\n"
      "  initial result = (\"\" == \"0\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elaboration, EmptyStringVsNulEscapeCompareElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic result;\n"
      "  initial result = (\"\" == \"\\0\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elaboration, EmptyStringInConditionalElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic r;\n"
      "  initial if (\"\") r = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
