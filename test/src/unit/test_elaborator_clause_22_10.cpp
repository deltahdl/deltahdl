#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(CelldefineElaboration, CelldefineModuleElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`celldefine\n"
      "module t;\n"
      "  parameter P = 1;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CelldefineElaboration, UnpairedCelldefineElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`celldefine\n"
      "module t;\n"
      "  parameter P = 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CelldefineElaboration, MultiplePairsElaborate) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`celldefine\n"
      "module m1;\n"
      "  parameter P = 10;\n"
      "endmodule\n"
      "`endcelldefine\n"
      "`celldefine\n"
      "module t;\n"
      "  parameter P = 20;\n"
      "endmodule\n"
      "`endcelldefine\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
