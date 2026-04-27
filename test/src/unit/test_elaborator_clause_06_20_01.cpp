

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

// §6.20.1: a class parameter without a default value must be supplied at every
// specialization. Using the unadorned class name picks the default
// specialization, which is invalid here.
TEST(ConstExprElab, ClassParamWithoutDefaultRequiresSpecialization) {
  EXPECT_FALSE(
      ElabOk("class D #(int p);\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  D obj;\n"
             "endmodule\n"));
}

// §6.20.1: an explicit specialization that supplies the missing parameter
// override is accepted.
TEST(ConstExprElab, ClassParamWithoutDefaultAcceptedWithExplicitOverride) {
  EXPECT_TRUE(
      ElabOk("class D #(int p);\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  D #(5) obj;\n"
             "endmodule\n"));
}

// §6.20.1: a parameter declared in a class body elaborates without error
// because the parameter keyword is treated as a synonym for localparam.
TEST(ConstExprElab, ClassBodyParameterElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  parameter int WIDTH = 8;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §6.20.1: multiple class-body parameters elaborate, including the case where
// one default expression depends on an earlier parameter.
TEST(ConstExprElab, ClassBodyParametersChainDependencies) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  parameter int A = 1;\n"
             "  parameter int B = A + 1;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §6.20.1: an empty parameter_port_list still triggers the rule that a body
// parameter behaves as a localparam.
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

// §6.20.1: a port-list value parameter without a default value must be
// supplied at every instantiation; the elaborator rejects an instance that
// fails to provide an override.
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

// §6.20.1: the same design element instantiated with an explicit override is
// accepted.
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

// §6.20.1: the elaborator shall not implicitly instantiate a portless nested
// design element whose parameter has no default value. Compilation succeeds
// because the nested module is simply skipped from implicit instantiation.
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
  // The nested module must not appear as a child instance of `outer`.
  for (const auto& child : design->top_modules[0]->children) {
    EXPECT_NE(child.module_name, "nested");
  }
}

// §6.20.1: a top-level design element with a no-default parameter cannot be
// implicitly instantiated as a top, so elaborating it as the root produces an
// error.
TEST(ConstExprElab, NoDefaultParamBlocksTopElaboration) {
  ElabFixture f;
  ElaborateSrc(
      "module top #(parameter int P)();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
