#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(PragmaElaboration, PragmaInsideModuleElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "  `pragma some_pragma\n"
      "  parameter P = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PragmaElaboration, PragmaBetweenModulesElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module m1;\n"
      "  parameter P = 10;\n"
      "endmodule\n"
      "`pragma some_pragma key = val\n"
      "module t;\n"
      "  parameter P = 20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PragmaElaboration, MultiplePragmasElaborate) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`pragma first_pragma\n"
      "module t;\n"
      "  `pragma second_pragma 42\n"
      "  parameter P = 5;\n"
      "endmodule\n"
      "`pragma third_pragma\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
