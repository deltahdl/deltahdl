#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(FileAndLineMacroElaboration, LineInAssignmentElaborates) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "  integer line_num;\n"
      "  initial line_num = `__LINE__;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FileAndLineMacroElaboration, FileInDisplayElaborates) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "  initial $display(\"File: %s\", `__FILE__);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FileAndLineMacroElaboration, BothInDisplayElaborates) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "  initial $display(\"at %s:%0d\", `__FILE__, `__LINE__);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
