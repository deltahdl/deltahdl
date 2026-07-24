#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ModuleInstanceParameterAssignment,
     OverrideSuppliesValueToInstanceParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.W(8)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "W");
  EXPECT_TRUE(u0->params[0].is_resolved);
  EXPECT_EQ(u0->params[0].resolved_value, 8);
}

TEST(ModuleInstanceParameterAssignment, UnknownParameterNameProducesError) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.NOPE(8)) u0();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ModuleInstanceParameterAssignment,
     PartialOverrideLeavesUnspecifiedAtDefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 1,\n"
      "               parameter int B = 2,\n"
      "               parameter int C = 3)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.B(20)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 3u);
  EXPECT_EQ(u0->params[0].name, "A");
  EXPECT_EQ(u0->params[0].resolved_value, 1);
  EXPECT_EQ(u0->params[1].name, "B");
  EXPECT_EQ(u0->params[1].resolved_value, 20);
  EXPECT_EQ(u0->params[2].name, "C");
  EXPECT_EQ(u0->params[2].resolved_value, 3);
}

TEST(ModuleInstanceParameterAssignment, EmptyExpressionRetainsDefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 7)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.W()) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "W");
  EXPECT_EQ(u0->params[0].resolved_value, 7);
}

// The value linked to a named parameter is an expression evaluated in the
// instantiating module's scope, not merely a literal. A parameter of the
// enclosing module is a valid constant form for that value (§6.20.2).
TEST(ModuleInstanceParameterAssignment,
     NamedOverrideValueMayBeParentParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "endmodule\n"
      "module top #(parameter int P = 12)();\n"
      "  child #(.W(P)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "W");
  EXPECT_TRUE(u0->params[0].is_resolved);
  EXPECT_EQ(u0->params[0].resolved_value, 12);
}

// A localparam of the enclosing module is another constant form (§6.20.2) that
// may supply a named override value; it flows through the same scope-evaluation
// path as a literal or parameter but is declared differently.
TEST(ModuleInstanceParameterAssignment,
     NamedOverrideValueMayBeParentLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  localparam int L = 9;\n"
      "  child #(.W(L)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "W");
  EXPECT_TRUE(u0->params[0].is_resolved);
  EXPECT_EQ(u0->params[0].resolved_value, 9);
}

// Named assignment also binds a TYPE parameter (§6.20.3): the operand of the
// override is a type rather than a value expression, taking a distinct code
// path. The chosen type propagates to declarations inside the child, so a
// variable typed by the parameter takes the overridden type's width.
TEST(ModuleInstanceParameterAssignment, TypeParameterNamedOverrideSelectsType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter type T = byte)();\n"
      "  T sig;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T(int)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  const RtlirVariable* sig = nullptr;
  for (const auto& v : u0->variables)
    if (v.name == "sig") sig = &v;
  ASSERT_NE(sig, nullptr);
  // int is 32 bits; the default byte would have been 8.
  EXPECT_EQ(sig->width, 32u);
}

TEST(ModuleInstanceParameterAssignment,
     DifferentInstancesMayUseDifferentMethods) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 1)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(8) u_ordered();\n"
      "  child #(.W(8)) u_named();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 2u);
  auto* u_ordered = top->children[0].resolved;
  auto* u_named = top->children[1].resolved;
  ASSERT_NE(u_ordered, nullptr);
  ASSERT_NE(u_named, nullptr);
  ASSERT_EQ(u_ordered->params.size(), 1u);
  ASSERT_EQ(u_named->params.size(), 1u);
  EXPECT_EQ(u_ordered->params[0].resolved_value, 8);
  EXPECT_EQ(u_named->params[0].resolved_value, 8);
}

}  // namespace
