#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(KeywordVersionElaboration, BeginKeywordsModuleElaborates) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`begin_keywords \"1800-2023\"\n"
      "module t;\n"
      "  parameter P = 1;\n"
      "endmodule\n"
      "`end_keywords\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(KeywordVersionElaboration, OldVersionIdentifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`begin_keywords \"1364-2001\"\n"
      "module t;\n"
      "  wire logic;\n"
      "endmodule\n"
      "`end_keywords\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(KeywordVersionElaboration, NestedBeginKeywordsElaborates) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`begin_keywords \"1800-2012\"\n"
      "`begin_keywords \"1364-2001\"\n"
      "module t;\n"
      "  wire logic;\n"
      "endmodule\n"
      "`end_keywords\n"
      "`end_keywords\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
