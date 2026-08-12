#include "fixture_elaborator.h"
#include "helpers_child_instance.h"

using namespace delta;

namespace {

TEST(ParameterDependence, LocalparamUpdatesWhenParamOverridden) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "  localparam int MASK = (1 << W) - 1;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.W(8)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* child = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child, nullptr);
  for (const auto& p : child->params) {
    if (p.name == "MASK") {
      EXPECT_TRUE(p.is_localparam);
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 255);
    }
  }
}

TEST(ParameterDependence, OverridePropagatesThroughDependencyChain) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2,\n"
      "               parameter int B = A * 3,\n"
      "               parameter int C = B + 1)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.A(5)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectResolvedParams(SoleChildInstance(design),
                       {{"A", 5}, {"B", 15}, {"C", 16}});
}

// §23.10.3 para 1: the dependence recompute holds no matter which §23.10.2
// instantiation form supplies the override. Here the source parameter is fixed
// by an ordered-list (positional) override -- a different resolution path than
// the by-name form -- and the two dependent parameters still track it.
TEST(ParameterDependence, OrderedListOverridePropagatesThroughDependencyChain) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2,\n"
      "               parameter int B = A * 3,\n"
      "               parameter int C = B + 1)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(5) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectResolvedParams(SoleChildInstance(design),
                       {{"A", 5}, {"B", 15}, {"C", 16}});
}

TEST(ParameterDependence, OverrideOfNonDependencyLeavesIndependentUnchanged) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 7,\n"
      "               parameter int B = 9)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.A(100)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 2u);
  EXPECT_EQ(u0->params[0].resolved_value, 100);
  EXPECT_EQ(u0->params[1].resolved_value, 9);
}

TEST(ParameterDependence, DefparamOverridePropagatesThroughDependencyChain) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2,\n"
      "               parameter int B = A * 3,\n"
      "               parameter int C = B + 1)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.A = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 3u);
  EXPECT_EQ(u0->params[0].resolved_value, 5);
  EXPECT_EQ(u0->params[1].resolved_value, 15);
  EXPECT_EQ(u0->params[2].resolved_value, 16);
}

TEST(ParameterDependence, DependentParamOwnInstanceOverrideBeatsSourceParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2,\n"
      "               parameter int B = A * 3)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.A(5), .B(100)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 2u);
  EXPECT_EQ(u0->params[0].resolved_value, 5);
  EXPECT_EQ(u0->params[1].resolved_value, 100);
}

TEST(ParameterDependence, DependentParamOwnDefparamOverrideBeatsSourceParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2,\n"
      "               parameter int B = A * 3)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.A = 5;\n"
      "  defparam u0.B = 100;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 2u);
  EXPECT_EQ(u0->params[0].resolved_value, 5);
  EXPECT_EQ(u0->params[1].resolved_value, 100);
}

TEST(ParameterDependence, RangeDependencyRecomputesOnOverride) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter P = 1,\n"
      "               parameter [P:0] Q = 0)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(7)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 2u);
  EXPECT_EQ(u0->params[1].name, "Q");
  EXPECT_EQ(u0->params[1].decl_width, 8u);
}

TEST(ParameterDependence, TypeParamOverrideRecomputesDependentVariableWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter type T = byte,\n"
      "               parameter T p = 7)();\n"
      "  T x;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T(shortint)) u0();\n"
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

// §23.10.3 states "It is possible for an override of a parameter to result in
// an illegal parameter assignment. For example, if T in the preceding example
// was overridden to a class type, the evaluation of p3 would be illegal and
// would cause elaboration to fail."
TEST(ParameterDependence, TypeOverrideToClassMakesDependentAssignmentIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "endclass\n"
      "module child #(parameter type T = int,\n"
      "               parameter T p = 7)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T(C)) u0();\n"
      "endmodule\n",
      f);
  const Diagnostic* diag =
      FindDiag(f,
               "cannot assign an integral value to parameter whose type "
               "parameter 'T' resolved to a class type");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "23.10.3");
}

// §23.10.3 states "if the type parameter T is not overridden to an integral
// type, the evaluation of the default value for parameter p is illegal". The
// source here is the standard's own example, with T left at its class default.
TEST(ParameterDependence, UnoverriddenClassTypeDefaultFailsElaboration) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "endclass\n"
      "module child #(parameter type T = C,\n"
      "               parameter T p = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "endmodule\n",
      f);
  const Diagnostic* diag =
      FindDiag(f,
               "cannot assign an integral value to parameter whose type "
               "parameter 'T' resolved to a class type");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "23.10.3");
}

TEST(ParameterDependence, TypeOverrideToIntegralMakesClassDefaultLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "endclass\n"
      "module child #(parameter type T = C,\n"
      "               parameter T p = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T(int)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §23.10.3 says of this source only that "since T2 requires an instantiation
// override, the evaluation of p2 shall only occur with the type defined by the
// parameter override". What makes the override compulsory is §6.20.1: "If no
// default value is specified for a parameter of a design element, then an
// overriding parameter value shall be specified in every instantiation of that
// design element", which is the rule the missing override is reported under.
TEST(ParameterDependence, NoDefaultTypeParamWithDependentRequiresOverride) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter type T2,\n"
      "               parameter T2 p2 = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "endmodule\n",
      f);
  const Diagnostic* diag =
      FindDiag(f,
               "type parameter 'T2' of 'child' has no default type and no "
               "override at instantiation");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.20.1");
}

// §23.10.3 para 4/5: when a no-default type parameter is overridden at
// instantiation, a value parameter that depends on it is evaluated only with
// the override type -- not merely "without error", but sized by that exact
// type. Two instances pick different override types, so the dependent
// parameter's own declared width tracks the override rather than a constant.
TEST(ParameterDependence,
     NoDefaultTypeParamSizesDependentParamFromOverrideType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter type T2,\n"
      "               parameter T2 p2 = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T2(byte)) u_byte();\n"
      "  child #(.T2(shortint)) u_short();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->children.size(), 2u);
  auto width_of_p2 = [](const auto* inst) -> uint32_t {
    for (const auto& p : inst->params) {
      if (p.name == "p2") return p.decl_width;
    }
    return 0;
  };
  auto* u_byte = design->top_modules[0]->children[0].resolved;
  auto* u_short = design->top_modules[0]->children[1].resolved;
  ASSERT_NE(u_byte, nullptr);
  ASSERT_NE(u_short, nullptr);
  EXPECT_EQ(width_of_p2(u_byte), 8u);
  EXPECT_EQ(width_of_p2(u_short), 16u);
}

}  // namespace
