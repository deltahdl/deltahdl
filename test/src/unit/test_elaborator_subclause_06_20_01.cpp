#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

TEST(ConstExprElab, NonConstantParamDefaultIsReportedAndLeftUnresolved) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter 'P' value is not a constant expression",
                            2, "6.20.2"));
  EXPECT_FALSE(design->top_modules[0]->params[0].is_resolved);
}

TEST(ConstExprElab, ClassParamWithoutDefaultRequiresSpecialization) {
  ElabFixture f;
  ElaborateSrc(
      "class D #(int p);\n"
      "  int data;\n"
      "endclass\n"
      "module m;\n"
      "  D obj;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameterized class 'D' has no default "
                            "specialization; parameter 'p' has no default "
                            "value",
                            5, "8.25"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter 'P' of 'child' has no default value and "
                            "no override at instantiation",
                            1, "6.20.1"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter 'P' of 'top' has no default value and "
                            "no override at instantiation",
                            1, "6.20.1"));
}

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
