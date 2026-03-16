#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(LineDirectiveElaboration, LineInsideModuleElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "  `line 50 \"other.sv\" 0\n"
      "  parameter P = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LineDirectiveElaboration, LineBetweenModulesElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module m1;\n"
      "  parameter P = 10;\n"
      "endmodule\n"
      "`line 100 \"switched.sv\" 0\n"
      "module t;\n"
      "  parameter P = 20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
