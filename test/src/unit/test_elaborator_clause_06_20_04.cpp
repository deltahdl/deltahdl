#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(LocalparamElaboration, LocalparamResolvesValue) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam int DEPTH = 32;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "DEPTH") {
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 32);
      EXPECT_TRUE(p.is_localparam);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(LocalparamElaboration, ParameterAndLocalparamCoexist) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "  localparam int DEPTH = 16;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found_width = false, found_depth = false;
  for (const auto& p : mod->params) {
    if (p.name == "WIDTH") {
      EXPECT_EQ(p.resolved_value, 8);
      EXPECT_FALSE(p.is_localparam);
      found_width = true;
    }
    if (p.name == "DEPTH") {
      EXPECT_EQ(p.resolved_value, 16);
      EXPECT_TRUE(p.is_localparam);
      found_depth = true;
    }
  }
  EXPECT_TRUE(found_width);
  EXPECT_TRUE(found_depth);
}

TEST(LocalparamElaboration, LocalparamDerivedFromParameter) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "  localparam int DOUBLE = WIDTH * 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "DOUBLE") {
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 16);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(LocalparamElaboration, ImplicitTypeLocalparamResolvesValue) {
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

TEST(LocalparamElaboration, DefparamOnLocalparamIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module child;\n"
      "  localparam int WIDTH = 4;\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.WIDTH = 16;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.20.4: a localparam cannot be modified by an instance parameter value
// assignment. A named override that targets a localparam port is rejected
// because the localparam is not an overridable parameter of the instance.
TEST(LocalparamElaboration, NamedInstanceOverrideOfLocalparamIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(localparam int LP = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.LP(9)) u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// §6.20.4: the same prohibition applies to positional overrides, which only
// target nonlocal parameters; supplying one when the port list has only a
// localparam is an error.
TEST(LocalparamElaboration, PositionalInstanceOverrideOfLocalparamIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(localparam int LP = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(9) u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// §6.20.4: a localparam is assigned a constant expression containing a
// parameter, which in turn can be modified by an instance parameter value
// assignment; the localparam follows the overridden parameter value.
TEST(LocalparamElaboration, LocalparamFollowsOverriddenParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 8);\n"
      "  localparam int W2 = W * 2;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.W(16)) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_FALSE(top->children.empty());
  auto* child = top->children[0].resolved;
  ASSERT_NE(child, nullptr);
  bool found = false;
  for (const auto& p : child->params) {
    if (p.name == "W2") {
      found = true;
      EXPECT_TRUE(p.is_localparam);
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 32);
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
