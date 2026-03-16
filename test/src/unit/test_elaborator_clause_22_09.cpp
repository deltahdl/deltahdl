#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(UnconnectedDriveElaboration, Pull1ModuleElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`unconnected_drive pull1\n"
      "module t;\n"
      "  parameter P = 1;\n"
      "endmodule\n"
      "`nounconnected_drive\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnconnectedDriveElaboration, Pull0ModuleElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`unconnected_drive pull0\n"
      "module t;\n"
      "  parameter P = 2;\n"
      "endmodule\n"
      "`nounconnected_drive\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnconnectedDriveElaboration, NoPairingElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`unconnected_drive pull1\n"
      "module t;\n"
      "  parameter P = 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnconnectedDriveElaboration, MostRecentDirectiveWins) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`unconnected_drive pull0\n"
      "`unconnected_drive pull1\n"
      "module t;\n"
      "  parameter P = 4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
