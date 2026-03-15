// Non-LRM tests

#include "fixture_elaborator.h"

namespace {

TEST(BuildingBlockElaboration, CuScopeTaskElaboratesSuccessfully) {
  EXPECT_TRUE(
      ElabOk("task my_task;\n"
             "endtask\n"
             "module m; endmodule\n"));
}

TEST(BuildingBlockElaboration, MultipleSameChildInstancesElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child; endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  child c2();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_GE(design->top_modules[0]->children.size(), 2u);
}

TEST(BuildingBlockElaboration, DiamondInstantiationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf; endmodule\n"
      "module mid1;\n"
      "  leaf l1();\n"
      "endmodule\n"
      "module mid2;\n"
      "  leaf l2();\n"
      "endmodule\n"
      "module top;\n"
      "  mid1 m1();\n"
      "  mid2 m2();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->children.size(), 2u);
}

}  // namespace
