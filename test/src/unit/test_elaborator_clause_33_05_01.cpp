#include "fixture_elaborator.h"

namespace {

TEST(SinglePassDescend, UnusedLibraryCellAbsentFromDesign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module unused;\n"
      "endmodule\n"
      "module child;\n"
      "endmodule\n"
      "module top;\n"
      "  child c();\n"
      "endmodule\n",
      f, "top");
  ASSERT_FALSE(f.has_errors);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_TRUE(design->all_modules.contains("top"));
  EXPECT_TRUE(design->all_modules.contains("child"));
  EXPECT_FALSE(design->all_modules.contains("unused"));
}

TEST(SinglePassDescend, TransitiveHierarchyFullyBound) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf;\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l();\n"
      "endmodule\n"
      "module top;\n"
      "  mid m();\n"
      "endmodule\n",
      f, "top");
  ASSERT_FALSE(f.has_errors);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->all_modules.size(), 3u);
  EXPECT_TRUE(design->all_modules.contains("top"));
  EXPECT_TRUE(design->all_modules.contains("mid"));
  EXPECT_TRUE(design->all_modules.contains("leaf"));
}

TEST(SinglePassDescend, UnreachableSubtreeStaysInLibrary) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module dead_leaf;\n"
      "endmodule\n"
      "module dead;\n"
      "  dead_leaf dl();\n"
      "endmodule\n"
      "module top;\n"
      "endmodule\n",
      f, "top");
  ASSERT_FALSE(f.has_errors);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->all_modules.size(), 1u);
  EXPECT_TRUE(design->all_modules.contains("top"));
  EXPECT_FALSE(design->all_modules.contains("dead"));
  EXPECT_FALSE(design->all_modules.contains("dead_leaf"));
}

TEST(SinglePassDescend, AlternateTopProducesAlternateDesign) {
  ElabFixture f1;
  auto* d1 = ElaborateSrc(
      "module helper;\n"
      "endmodule\n"
      "module rootA;\n"
      "  helper h();\n"
      "endmodule\n"
      "module rootB;\n"
      "endmodule\n",
      f1, "rootA");
  ASSERT_FALSE(f1.has_errors);
  ASSERT_NE(d1, nullptr);
  EXPECT_EQ(d1->top_modules[0]->name, "rootA");
  EXPECT_TRUE(d1->all_modules.contains("helper"));
  EXPECT_FALSE(d1->all_modules.contains("rootB"));

  ElabFixture f2;
  auto* d2 = ElaborateSrc(
      "module helper;\n"
      "endmodule\n"
      "module rootA;\n"
      "  helper h();\n"
      "endmodule\n"
      "module rootB;\n"
      "endmodule\n",
      f2, "rootB");
  ASSERT_FALSE(f2.has_errors);
  ASSERT_NE(d2, nullptr);
  EXPECT_EQ(d2->top_modules[0]->name, "rootB");
  EXPECT_FALSE(d2->all_modules.contains("helper"));
  EXPECT_FALSE(d2->all_modules.contains("rootA"));
}

TEST(SinglePassDescend, InstanceWithNoLibraryEntryFails) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  not_in_library u();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

}
