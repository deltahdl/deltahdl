

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(ConstExprElab, BodyParameterPromotedWithPortList) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int W = 8);\n"
      "  parameter int MASK = 255;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  bool found = false;
  for (auto& pd : design->top_modules[0]->params) {
    if (pd.name == "MASK") {
      found = true;
      EXPECT_TRUE(pd.is_localparam);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ConstExprElab, PortListParameterDependsOnEarlier) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int N = 4, parameter int N2 = N * 2);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& p = design->top_modules[0]->params[1];
  EXPECT_EQ(p.name, "N2");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 8);
}

TEST(ConstExprElab, NonConstantParamDefaultWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  EXPECT_FALSE(design->top_modules[0]->params[0].is_resolved);
}

TEST(ConstExprElab, ClassParamWithoutDefaultRequiresSpecialization) {
  EXPECT_FALSE(
      ElabOk("class D #(int p);\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  D obj;\n"
             "endmodule\n"));
}

TEST(ConstExprElab, ClassParamWithoutDefaultAcceptedWithExplicitOverride) {
  EXPECT_TRUE(
      ElabOk("class D #(int p);\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  D #(5) obj;\n"
             "endmodule\n"));
}

TEST(ConstExprElab, ClassBodyParameterElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  parameter int WIDTH = 8;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(ConstExprElab, ClassBodyParametersChainDependencies) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  parameter int A = 1;\n"
             "  parameter int B = A + 1;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(ConstExprElab, BodyParameterPromotedWithEmptyPortList) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #();\n"
      "  parameter int P = 1;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  bool found = false;
  for (auto& pd : design->top_modules[0]->params) {
    if (pd.name == "P") {
      found = true;
      EXPECT_TRUE(pd.is_localparam);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ConstExprElab, PortListParameterWithoutDefaultRejectsMissingOverride) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter int P)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstExprElab, PortListParameterWithoutDefaultAcceptedWithOverride) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(7)) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstExprElab, NoDefaultParamSuppressesImplicitNestedInstantiation) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module outer;\n"
      "  module nested #(parameter int P)();\n"
      "  endmodule\n"
      "endmodule\n",
      f, "outer");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  for (const auto& child : design->top_modules[0]->children) {
    EXPECT_NE(child.module_name, "nested");
  }
}

TEST(ConstExprElab, NoDefaultParamBlocksTopElaboration) {
  ElabFixture f;
  ElaborateSrc(
      "module top #(parameter int P)();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// §6.20.1: in a list of parameter constants a parameter may depend on an
// earlier one, and the list may interleave value and type parameters (the
// clause's own example: N, then M depending on N, then a type parameter T, then
// a value parameter x of that type). Driven through elaboration: M resolves to
// N*16 even with a type parameter following it, and the type-parameter-typed
// value parameter x resolves to its default.
TEST(ConstExprElab, PortListMixedValueAndTypeDependencies) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module mc #(int N = 5, M = N * 16, type T = int, T x = 0)();\n"
      "endmodule\n",
      f, "mc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirParamDecl* m = nullptr;
  const RtlirParamDecl* x = nullptr;
  for (const auto& p : design->top_modules[0]->params) {
    if (p.name == "M") m = &p;
    if (p.name == "x") x = &p;
  }
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_resolved);
  EXPECT_EQ(m->resolved_value, 80);
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_resolved);
  EXPECT_EQ(x->resolved_value, 0);
}

}  // namespace
