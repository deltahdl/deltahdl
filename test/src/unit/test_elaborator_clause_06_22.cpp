#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(TypeCompatibilityElaboration, AssignIntToLogicVector) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  logic [31:0] y;\n"
      "  initial y = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TypeCompatibilityElaboration, AssignRealToInt) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  int i;\n"
      "  initial i = r;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TypeCompatibilityElaboration, MatchingTypesSameTypedef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  byte_t a;\n"
      "  byte_t b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TypeCompatibilityElaboration, IntAndBitSignedAreInterchangeable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  bit signed [31:0] y;\n"
      "  initial begin\n"
      "    x = y;\n"
      "    y = x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TypeCompatibilityElaboration, TypeIncompatibleStringToInt) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  string s;\n"
      "  int i;\n"
      "  initial i = s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
