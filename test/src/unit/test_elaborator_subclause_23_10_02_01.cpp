#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(OrderedListParameterAssignment, PositionalValuesMapInDeclarationOrder) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2,\n"
      "               parameter int B = 3)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(10, 15) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 2u);
  EXPECT_EQ(u0->params[0].name, "A");
  EXPECT_EQ(u0->params[0].resolved_value, 10);
  EXPECT_EQ(u0->params[1].name, "B");
  EXPECT_EQ(u0->params[1].resolved_value, 15);
}

TEST(OrderedListParameterAssignment,
     SinglePositionalValueOverridesFirstParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 1)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(42) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].resolved_value, 42);
}

TEST(OrderedListParameterAssignment,
     PartialSubsetKeepsTrailingParametersAtDeclaredDefaults) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2,\n"
      "               parameter int B = 3,\n"
      "               parameter int C = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(10) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 3u);
  EXPECT_EQ(u0->params[0].resolved_value, 10);
  EXPECT_EQ(u0->params[1].resolved_value, 3);
  EXPECT_EQ(u0->params[2].resolved_value, 4);
}

TEST(OrderedListParameterAssignment, EmptyOrderedListKeepsAllDeclaredDefaults) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 7,\n"
      "               parameter int B = 9)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #() u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 2u);
  EXPECT_EQ(u0->params[0].resolved_value, 7);
  EXPECT_EQ(u0->params[1].resolved_value, 9);
}

TEST(OrderedListParameterAssignment, TooManyPositionalValuesRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(10, 15) u0();\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(f.has_errors);
}

TEST(OrderedListParameterAssignment,
     LocalparamInParameterPortListExcludedFromOrderedList) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 1,\n"
      "               localparam int L = 10,\n"
      "               parameter int B = 2)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(5, 6) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 3u);
  for (const auto& p : u0->params) {
    if (p.name == "A") {
      EXPECT_FALSE(p.is_localparam);
      EXPECT_EQ(p.resolved_value, 5);
    } else if (p.name == "L") {
      EXPECT_TRUE(p.is_localparam);
      EXPECT_EQ(p.resolved_value, 10);
    } else if (p.name == "B") {
      EXPECT_FALSE(p.is_localparam);
      EXPECT_EQ(p.resolved_value, 6);
    }
  }
}

TEST(OrderedListParameterAssignment,
     OrderedListCountedAgainstNonLocalparamsOnly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 1,\n"
      "               localparam int L = 99,\n"
      "               parameter int B = 2)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(7, 8, 9) u0();\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(f.has_errors);
}

// §23.10.2.1: an ordered override value is a constant expression evaluated in
// the instantiating scope. Building it from a value parameter of the parent
// (§6.20.2) instead of a literal drives the constant-evaluation scope-lookup
// path, while the same positional declaration-order binding rule applies.
TEST(OrderedListParameterAssignment,
     PositionalOverrideValueFromInstantiatingParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2)();\n"
      "endmodule\n"
      "module top;\n"
      "  parameter int P = 12;\n"
      "  child #(P) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "A");
  EXPECT_EQ(u0->params[0].resolved_value, 12);
}

// Same ordered-binding rule, but the override value is produced by a localparam
// of the parent (§6.20.4). A localparam is a valid constant source for the
// override even though a localparam cannot itself be overridden.
TEST(OrderedListParameterAssignment,
     PositionalOverrideValueFromInstantiatingLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2)();\n"
      "endmodule\n"
      "module top;\n"
      "  localparam int Q = 20;\n"
      "  child #(Q) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "A");
  EXPECT_EQ(u0->params[0].resolved_value, 20);
}

// §23.10.2.1 lets the ordered list assign values *or types* by position. A type
// parameter (§6.20.3) sits at position 0 here, so the ordered type argument
// overrides it; the effect is observed through the width of a variable declared
// with that type in the resolved child (byte default 8 -> shortint override
// 16).
TEST(OrderedListParameterAssignment,
     PositionalTypeParameterOverrideAppliesInDeclarationOrder) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter type T = byte)();\n"
      "  T x;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(shortint) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_GE(u0->variables.size(), 1u);
  EXPECT_EQ(u0->variables[0].name, "x");
  EXPECT_EQ(u0->variables[0].width, 16u);
}

}  // namespace
