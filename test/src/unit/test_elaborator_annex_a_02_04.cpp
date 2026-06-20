#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DeclarationAssignmentElaboration, NetDeclAssignmentWithUnpackedDims) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w [3:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->nets.size(), 1u);
}

TEST(DeclarationAssignmentElaboration, ParamAssignmentResolvesConstant) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter WIDTH = 8;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "WIDTH") {
      found = true;
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 8);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationAssignmentElaboration, ParamAssignmentNoDefaultInPort) {
  EXPECT_TRUE(
      ElabOk("module child #(parameter int P = 1)(); endmodule\n"
             "module m; child #(.P(10)) c(); endmodule\n"));
}

TEST(DeclarationAssignmentElaboration, TypeAssignmentRegistersType) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter type T = int;\n"
             "  T x = 5;\n"
             "endmodule\n"));
}

TEST(DeclarationAssignmentElaboration, TypeAssignmentNoDefaultInPort) {
  EXPECT_TRUE(
      ElabOk("module child #(parameter type T = int)();\n"
             "  T x = 0;\n"
             "endmodule\n"
             "module m; child c(); endmodule\n"));
}

TEST(DeclarationAssignmentElaboration, VarDeclAssignmentPreservesInit) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int x = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "x") {
      found = true;
      EXPECT_NE(v.init_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationAssignmentElaboration, VarDeclAssignmentWithUnpackedDims) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int arr [0:3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "arr") {
      found = true;
      EXPECT_EQ(v.unpacked_size, 4u);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationAssignmentElaboration, VarDeclAssignmentDynamicArray) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int d[];\n"
             "endmodule\n"));
}

TEST(DeclarationAssignmentElaboration, VarDeclAssignmentClassVariable) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(DeclarationAssignmentElaboration, DefparamAssignmentOverridesChildParam) {
  ElabFixture f;
  auto* design = Elaborate(
      "module child;\n"
      "  parameter P = 1;\n"
      "endmodule\n"
      "module m;\n"
      "  child c();\n"
      "  defparam c.P = 42;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_FALSE(top->children.empty());
  auto* inst = top->children[0].resolved;
  ASSERT_NE(inst, nullptr);
  bool found = false;
  for (auto& p : inst->params) {
    if (p.name == "P") {
      found = true;
      EXPECT_TRUE(p.is_resolved);
      EXPECT_TRUE(p.from_override);
      EXPECT_EQ(p.resolved_value, 42);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationAssignmentElaboration, DefparamAssignmentDeepHierarchy) {
  ElabFixture f;
  auto* design = Elaborate(
      "module leaf;\n"
      "  parameter P = 1;\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l();\n"
      "endmodule\n"
      "module m;\n"
      "  mid mi();\n"
      "  defparam mi.l.P = 99;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_FALSE(top->children.empty());
  auto* mid_inst = top->children[0].resolved;
  ASSERT_NE(mid_inst, nullptr);
  ASSERT_FALSE(mid_inst->children.empty());
  auto* leaf_inst = mid_inst->children[0].resolved;
  ASSERT_NE(leaf_inst, nullptr);
  bool found = false;
  for (auto& p : leaf_inst->params) {
    if (p.name == "P") {
      found = true;
      EXPECT_TRUE(p.is_resolved);
      EXPECT_TRUE(p.from_override);
      EXPECT_EQ(p.resolved_value, 99);
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
