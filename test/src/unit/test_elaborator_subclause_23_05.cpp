#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

namespace {

TEST(ExternModuleElaboration, ExternDeclarationSkippedForInstantiation) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module child(input logic a, output logic b);\n"
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top(input logic a, output logic b);\n"
      "  child u0(.a(a), .b(b));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* child = top->children[0].resolved;
  ASSERT_NE(child, nullptr);
  EXPECT_FALSE(child->assigns.empty());
}

TEST(ExternModuleElaboration, ExternDeclarationDoesNotDuplicatePorts) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module m(input logic a, output logic b);\n"
      "module m(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  EXPECT_EQ(top->ports.size(), 2u);
  EXPECT_FALSE(top->assigns.empty());
}

TEST(ExternModuleElaboration, WildcardPortsResolveDirections) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module m(input logic a, output logic b);\n"
      "module m(.*);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->ports.size(), 2u);
  EXPECT_EQ(top->ports[0].direction, Direction::kInput);
  EXPECT_EQ(top->ports[1].direction, Direction::kOutput);
}

TEST(ExternModuleElaboration, WildcardPortsWithParametersFromExtern) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module m #(parameter W = 8)\n"
      "  (input logic [W-1:0] a, output logic [W-1:0] b);\n"
      "module m(.*);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  EXPECT_FALSE(top->params.empty());
  ASSERT_EQ(top->ports.size(), 2u);
}

// §23.5: `.*` places the extern declaration's parameters on the module. A type
// parameter follows a different code path than a value parameter (its default
// type is carried in a parallel array), so exercise it as a distinct input form
// and observe that the type parameter itself is placed on the module.
TEST(ExternModuleElaboration, WildcardImportsTypeParameterFromExtern) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module m #(parameter type TP = logic [7:0])\n"
      "  (input TP a, output TP b);\n"
      "module m(.*);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->ports.size(), 2u);
  bool has_type_param = false;
  for (const auto& p : top->params) {
    if (p.name == "TP" && p.is_type_param) has_type_param = true;
  }
  EXPECT_TRUE(has_type_param);
}

TEST(ExternModuleElaboration, WildcardModuleInstantiatedFromParent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module child(input logic [7:0] a, output logic [7:0] b);\n"
      "module child(.*);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  child u0(.a(a), .b(b));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* child = top->children[0].resolved;
  ASSERT_NE(child, nullptr);
  EXPECT_EQ(child->ports.size(), 2u);
}

// §23.5: an extern module declaration can appear at any level of the
// instantiation hierarchy and only declares ports. A nested extern declaration
// must not be elaborated as an instantiable module nor shadow the actual nested
// definition of the same name. The extern is declared after the real module so
// that keeping it out of the nested-module table is observable: were it
// applied, the empty extern would displace the real body and drop the assign.
TEST(ExternModuleElaboration, NestedExternDoesNotShadowDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic x, y;\n"
      "  module child(input logic a, output logic b);\n"
      "    assign b = a;\n"
      "  endmodule\n"
      "  extern module child(input logic a, output logic b);\n"
      "  child u0(.a(x), .b(y));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* child = top->children[0].resolved;
  ASSERT_NE(child, nullptr);
  EXPECT_EQ(child->ports.size(), 2u);
  EXPECT_FALSE(child->assigns.empty());
}

// §23.5: the LRM's own example for the `.*` module header uses a NON-ANSI
// extern declaration (port names only); the module body then supplies the
// directions via non-ANSI port declarations. Placing the extern's ports on the
// module and letting the body declarations give their directions shall yield
// the same module as writing the names in the header directly.
TEST(ExternModuleElaboration, WildcardHeaderNonAnsiExternBodyDirections) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module m(a, b, c, d);\n"
      "module m(.*);\n"
      "  input a, b, c;\n"
      "  output d;\n"
      "  assign d = a & b & c;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->ports.size(), 4u);
  EXPECT_EQ(top->ports[0].direction, Direction::kInput);
  EXPECT_EQ(top->ports[1].direction, Direction::kInput);
  EXPECT_EQ(top->ports[2].direction, Direction::kInput);
  EXPECT_EQ(top->ports[3].direction, Direction::kOutput);
}

TEST(ExternModuleElaboration, PortCountMismatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "extern module m(input logic a, output logic b);\n"
      "module m(input logic a);\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "module 'm' port count (1) does not match extern declaration (2)", 2,
      "23.5"));
}

TEST(ExternModuleElaboration, PortNameMismatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "extern module m(input logic a, output logic b);\n"
      "module m(input logic x, output logic y);\n"
      "  assign y = x;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'm' port 'x' at position 0 does not match "
                            "extern declaration port 'a'",
                            2, "23.5"));
}

TEST(ExternModuleElaboration, ParamCountMismatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "extern module m #(parameter W = 8)\n"
      "  (input logic a, output logic b);\n"
      "module m(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "module 'm' parameter count (0) does not match extern declaration (1)", 3,
      "23.5"));
}

TEST(ExternModuleElaboration, PortDirectionMismatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "extern module m(input logic a, output logic b);\n"
      "module m(output logic a, output logic b);\n"
      "  assign b = 1'b0;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "module 'm' port 'a' direction does not match extern declaration", 2,
      "23.5"));
}

TEST(ExternModuleElaboration, PortTypeMismatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "extern module m(input logic a, output logic b);\n"
      "module m(input integer a, output logic b);\n"
      "  assign b = 1'b0;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "module 'm' port 'a' type does not match extern declaration", 2, "23.5"));
}

TEST(ExternModuleElaboration, NonAnsiExternPortsSkipTypeCheck) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module m(a, b);\n"
      "module m(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExternModuleElaboration, ParamNameMismatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "extern module m #(parameter W = 8)\n"
      "  (input logic a, output logic b);\n"
      "module m #(parameter N = 8)\n"
      "  (input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "module 'm' parameter 'N' at position 0 does not match "
                    "extern declaration parameter 'W'",
                    3, "23.5"));
}

TEST(ExternModuleElaboration, MatchingParamNamesNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module m #(parameter W = 8)\n"
      "  (input logic a, output logic b);\n"
      "module m #(parameter W = 8)\n"
      "  (input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExternModuleElaboration, PortSignednessMismatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "extern module m(input logic signed [3:0] a, output logic b);\n"
      "module m(input logic [3:0] a, output logic b);\n"
      "  assign b = a[0];\n"
      "endmodule\n",
      f, "m");
  // §23.5 requires equivalent port types, and signedness is part of the type,
  // so a signedness difference is reported as the type mismatch it is.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "module 'm' port 'a' type does not match extern declaration", 2, "23.5"));
}

TEST(ExternModuleElaboration, ParamKindMismatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "extern module m #(parameter type TP = logic)\n"
      "  (input logic a, output logic b);\n"
      "module m #(parameter TP = 1)\n"
      "  (input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "module 'm' parameter 'TP' at position 0 does not match "
                    "the parameter kind of the extern declaration",
                    3, "23.5"));
}

TEST(ExternModuleElaboration, MatchingTypeParamNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module m #(parameter type TP = logic)\n"
      "  (input logic a, output logic b);\n"
      "module m #(parameter type TP = logic)\n"
      "  (input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §23.5: the extern declaration and the module match in parameter types, so
// a value parameter declared int in the one and logic [3:0] in the other is
// reported; written with the same type in both, or with no type in one of
// them, where the parameter takes its value's type (§6.20.2), it is not.
TEST(ExternModuleElaboration, ValueParamTypeMismatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "extern module a #(parameter int size = 8) (input logic [7:0] x);\n"
      "module a #(parameter logic [3:0] size = 8) (input logic [7:0] x);\n"
      "endmodule\n"
      "extern module b #(parameter int w = 8, parameter n = 2) ();\n"
      "module b #(parameter int w = 8, parameter int n = 2) ();\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  a ua(x);\n"
      "  b ub();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'a' parameter 'size' at position 0 is "
                            "declared with a data type not equivalent",
                            2, "23.5"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "module 'b' parameter", 5, "23.5"));
}

// §23.5: a localparam of the extern declaration's parameter port list stays
// local on the `.*` module that takes the header, so an instance's parameter
// value assignment naming it is refused, as §23.10.2.2 refuses one naming a
// localparam port of a module that declares the list itself.
TEST(ExternModuleElaboration, WildcardKeepsExternLocalparamPortLocal) {
  ElabFixture f;
  ElaborateSrc(
      "extern module a #(parameter int W = 4, localparam int L = W * 2)\n"
      "  (input logic [W-1:0] x);\n"
      "module a (.*);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  a #(.W(8), .L(3)) u (.x(x));\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'a' has no parameter 'L'", 7, "23.10.2.2"));
}

TEST(ExternModuleElaboration, WildcardExternLocalparamPortFollowsParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module a #(parameter int W = 4, localparam int L = W * 2)\n"
      "  (input logic [W-1:0] x);\n"
      "module a (.*);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  a #(.W(8)) u (.x(x));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* child = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child, nullptr);
  bool found = false;
  for (const auto& p : child->params) {
    if (p.name == "L") {
      found = true;
      EXPECT_TRUE(p.is_localparam);
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 16);
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
