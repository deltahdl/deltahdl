#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(Elaboration, PortBinding_UnknownModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic x;\n"
      "  nonexistent u0(.a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  EXPECT_EQ(mod->children[0].resolved, nullptr);
}

TEST(BuildingBlockElaboration, ModuleWithChildInstanceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child; endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_FALSE(design->top_modules[0]->children.empty());
}

TEST(BuildingBlockElaboration, NestedHierarchyTwoLevelsDeep) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf; endmodule\n"
      "module mid;\n"
      "  leaf l1();\n"
      "endmodule\n"
      "module top;\n"
      "  mid m1();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->name, "top");
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

TEST(ModuleInstantiation, TwoLevelHierarchyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  sub u0(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_FALSE(design->top_modules[0]->children.empty());
}

}  // namespace
