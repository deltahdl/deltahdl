// §23.3.1

#include "fixture_elaborator.h"

namespace {

TEST(TopLevelModules, EmptySourceTopNotFoundReturnsNull) {
  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>", "");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate("top");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(TopLevelModules, ElaboratedDesignContainsTopModule) {
  ElabFixture f;
  auto* design = ElaborateSrc("module top; endmodule", f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(TopLevelModules, SelectSpecificTopFromMultipleModules) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n",
      f, "b");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "b");
}

TEST(TopLevelModules, NonexistentTopIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module a; endmodule\n"
      "module b; endmodule\n",
      f, "nonexistent");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(TopLevelModules, UnknownTopIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; endmodule\n", f, "nonexistent");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(TopLevelModules, InstantiatedModuleIsNotTopLevel) {
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
  for (auto* m : design->top_modules) {
    EXPECT_NE(m->name, "child");
  }
}

TEST(TopLevelModules, TopLevelInstanceNameEqualsModuleName) {
  ElabFixture f;
  auto* design = ElaborateSrc("module my_top; endmodule\n", f, "my_top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "my_top");
}

TEST(TopLevelModules, TopLevelModuleInstantiatedExactlyOnce) {
  ElabFixture f;
  auto* design = ElaborateSrc("module top; endmodule\n", f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules.size(), 1u);
}

TEST(TopLevelModules, ModuleInGenerateBlockNotTopLevel) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child; endmodule\n"
      "module wrapper;\n"
      "  generate\n"
      "    child c1();\n"
      "  endgenerate\n"
      "endmodule\n"
      "module top;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  for (auto* m : design->top_modules) {
    EXPECT_NE(m->name, "child");
  }
}

TEST(TopLevelModules, ModuleInNonInstantiatedGenerateBlockNotTopLevel) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child; endmodule\n"
      "module unused;\n"
      "  generate\n"
      "    if (1) child c1();\n"
      "  endgenerate\n"
      "endmodule\n"
      "module top;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  for (auto* m : design->top_modules) {
    EXPECT_NE(m->name, "child");
  }
}

TEST(TopLevelModules, DollarRootRefResolvesToTopInstance) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module top;\n"
      "  logic [7:0] x;\n"
      "  assign x = $root.top.x;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TopLevelModules, DollarRootMultiLevelPathResolves) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module child;\n"
      "  logic sig;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic x;\n"
      "  assign x = $root.top.c1.sig;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
