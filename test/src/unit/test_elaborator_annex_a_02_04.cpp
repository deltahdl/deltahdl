#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- net_decl_assignment ---

TEST(DeclarationAssignmentElaboration, NetDeclAssignmentCreatesContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->assigns.size(), 1u);
}

TEST(DeclarationAssignmentElaboration, NetDeclAssignmentNoInit) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->assigns.size(), 0u);
}

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

// --- param_assignment ---

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

TEST(DeclarationAssignmentElaboration, ParamAssignmentLocalparam) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam X = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "X") {
      found = true;
      EXPECT_TRUE(p.is_localparam);
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 42);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationAssignmentElaboration, ParamAssignmentNoDefaultInPort) {
  EXPECT_TRUE(ElabOk(
      "module child #(parameter int P = 1)(); endmodule\n"
      "module m; child #(.P(10)) c(); endmodule\n"));
}

// --- specparam_assignment ---

TEST(DeclarationAssignmentElaboration, SpecparamCreatesVariable) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specify specparam tRISE = 100; endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "tRISE") {
      found = true;
      EXPECT_NE(v.init_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

// --- type_assignment ---

TEST(DeclarationAssignmentElaboration, TypeAssignmentRegistersType) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  parameter type T = int;\n"
      "  T x = 5;\n"
      "endmodule\n"));
}

TEST(DeclarationAssignmentElaboration, TypeAssignmentNoDefaultInPort) {
  EXPECT_TRUE(ElabOk(
      "module child #(parameter type T = int)();\n"
      "  T x = 0;\n"
      "endmodule\n"
      "module m; child c(); endmodule\n"));
}

// --- variable_decl_assignment ---

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
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  int d[];\n"
      "endmodule\n"));
}

TEST(DeclarationAssignmentElaboration, VarDeclAssignmentClassVariable) {
  EXPECT_TRUE(ElabOk(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n"));
}

// --- defparam_assignment ---

TEST(DeclarationAssignmentElaboration, DefparamResolvesValue) {
  ElabFixture f;
  auto* design = Elaborate(
      "module child; parameter P = 1; endmodule\n"
      "module m; child c(); defparam c.P = 99; endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* child_mod = design->all_modules["child"];
  if (child_mod) {
    for (auto& p : child_mod->params) {
      if (p.name == "P") {
        EXPECT_EQ(p.resolved_value, 99);
      }
    }
  }
}

}  // namespace
