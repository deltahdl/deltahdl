#include "fixture_elaborator.h"

namespace {

// --- Req 1: A module can be declared within another module ---

TEST(NestedModuleElaboration, NestedModuleDoesNotAffectParent) {
  ElabFixture f;
  auto* design = Elaborate(
      "module inner; endmodule\n"
      "module m;\n"
      "  module inner_nested; endmodule\n"
      "  wire a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NestedModuleElaboration, NestedModuleWithBodyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module inner;\n"
      "    wire a;\n"
      "    assign a = 1;\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NestedModuleElaboration, DeepNestingElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module mid;\n"
      "    module deep;\n"
      "    endmodule\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NestedModuleElaboration, MultipleNestedModulesElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module a; endmodule\n"
      "  module b; endmodule\n"
      "  module c; endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- Req 2: Outer scope visibility / local name shadowing ---

TEST(NestedModuleElaboration, OuterScopeWireVisibleInNestedModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  module inner;\n"
      "    assign w = 1'b1;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NestedModuleElaboration, OuterParameterVisibleInNestedModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam int W = 8;\n"
      "  module inner;\n"
      "    wire [W-1:0] bus;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NestedModuleElaboration, LocalNameShadowsOuterName) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  module inner;\n"
      "    wire w;\n"
      "    assign w = 1'b0;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- Req 3: Same module name in different scopes ---

TEST(NestedModuleElaboration, SameNameInDifferentParents) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top;\n"
      "  module a;\n"
      "    module helper; endmodule\n"
      "  endmodule\n"
      "  module b;\n"
      "    module helper; endmodule\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- Req 4: Portless nested modules implicitly instantiated ---

TEST(NestedModuleElaboration, PortlessNestedModuleImplicitlyInstantiated) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module inner;\n"
      "    wire w;\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_EQ(mod->children[0].module_name, "inner");
  EXPECT_EQ(mod->children[0].inst_name, "inner");
}

TEST(NestedModuleElaboration, MultiplePortlessImplicitlyInstantiated) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module a;\n"
      "    wire w;\n"
      "  endmodule\n"
      "  module b;\n"
      "    wire w;\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 2u);
}

TEST(NestedModuleElaboration, PortlessExplicitlyInstantiatedNotDuplicated) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module inner;\n"
      "    wire w;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_EQ(mod->children[0].inst_name, "i1");
}

// --- Req 5: Ported nested modules not instantiated are ignored ---

TEST(NestedModuleElaboration, PortedNestedModuleNotInstantiatedIsIgnored) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module inner(input a, output b);\n"
      "    assign b = a;\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(design->top_modules[0]->children.empty());
}

TEST(NestedModuleElaboration, PortedNestedModuleExplicitlyInstantiated) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire x, y;\n"
      "  module inner(input a, output b);\n"
      "    assign b = a;\n"
      "  endmodule\n"
      "  inner i1(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->children.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->children[0].module_name, "inner");
  EXPECT_EQ(design->top_modules[0]->children[0].inst_name, "i1");
}

// --- Mixed: portless and ported in same parent ---

TEST(NestedModuleElaboration, MixedPortlessAndPortedNested) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module portless;\n"
      "    wire w;\n"
      "  endmodule\n"
      "  module ported(input a);\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_EQ(mod->children[0].module_name, "portless");
  EXPECT_EQ(mod->children[0].inst_name, "portless");
}

}  // namespace
