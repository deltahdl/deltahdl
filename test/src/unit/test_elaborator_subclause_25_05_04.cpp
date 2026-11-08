#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ModportExpressionElaboration, SamePortIdInDifferentModports) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  logic [7:0] r;\n"
             "  modport A(output .P(r[3:0]));\n"
             "  modport B(output .P(r[7:4]));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

TEST(ModportExpressionElaboration, DuplicatePortIdInSameModportErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  logic a, b;\n"
      "  modport mp(input .P(a), input .P(b));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate port-id 'P' in modport 'mp'", 3,
                            "25.5.4"));
}

TEST(ModportExpressionElaboration,
     ConstantPortExpressionWithOutputDirectionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  modport mp(output .P(2));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "port-id 'P' in modport 'mp' has a constant port "
                            "expression and cannot be declared as output or "
                            "inout",
                            2, "25.5.4"));
}

TEST(ModportExpressionElaboration,
     ConstantPortExpressionWithInputDirectionAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  modport mp(input .P(2));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

TEST(ModportExpressionElaboration,
     ParameterPortExpressionWithOutputDirectionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface I #(parameter K = 3) ();\n"
      "  modport mp(output .P(K));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "port-id 'P' in modport 'mp' has a constant port "
                            "expression and cannot be declared as output or "
                            "inout",
                            2, "25.5.4"));
}

TEST(ModportExpressionElaboration,
     LocalparamPortExpressionWithOutputDirectionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  localparam L = 5;\n"
      "  modport mp(inout .P(L));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "port-id 'P' in modport 'mp' has a constant port "
                            "expression and cannot be declared as output or "
                            "inout",
                            3, "25.5.4"));
}

TEST(ModportExpressionElaboration,
     ConstVariablePortExpressionWithOutputDirectionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  const int x = 1;\n"
      "  modport mp(output .Q(x));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "port-id 'Q' in modport 'mp' has a constant port "
                            "expression and cannot be declared as output or "
                            "inout",
                            3, "25.5.4"));
}

TEST(ModportExpressionElaboration,
     ParameterPortExpressionWithInputDirectionAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I #(parameter K = 3) ();\n"
             "  modport mp(input .P(K));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

TEST(ModportExpressionElaboration,
     ConstVariablePortExpressionWithInputDirectionAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  const int x = 1;\n"
             "  modport mp(input .Q(x));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

TEST(ModportExpressionElaboration,
     PartSelectOfVariablePortExpressionWithOutputAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  logic [7:0] r;\n"
             "  modport mp(output .P(r[3:0]));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

TEST(ModportExpressionElaboration,
     ConcatenationPortExpressionWithOutputAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  logic a, b;\n"
             "  modport mp(output .P({a, b}));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

TEST(ModportExpressionElaboration,
     StructElementPortExpressionWithOutputAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  struct packed { logic x; logic y; } s;\n"
             "  modport mp(output .P(s.x));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

TEST(ModportExpressionElaboration, EmptyNamedPortNeedNotBeDeclared) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  modport mp(input .P());\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

TEST(ModportExpressionElaboration, BareSimplePortMustBeDeclared) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  modport mp(input P);\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "modport 'mp' references 'P', which interface 'I' does not declare", 2,
      "25.5"));
}

TEST(ModportExpressionElaboration, AssignmentPatternPortExpressionAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  logic a, b;\n"
             "  modport mp(input .P('{a, b}));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

TEST(ModportExpressionElaboration,
     LocalparamPortExpressionWithInputDirectionAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  localparam L = 5;\n"
             "  modport mp(input .P(L));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

TEST(ModportExpressionElaboration, SimplePortIdCollidingWithNamedPortIdErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  logic R, a;\n"
      "  modport mp(input R, output .R(a));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate port-id 'R' in modport 'mp'", 3,
                            "25.5.4"));
}

TEST(ModportExpressionElaboration,
     HierarchicalAccessThroughModportSelectsBoundExpression) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  logic [7:0] r;\n"
             "  modport A(output .P(r[3:0]));\n"
             "endinterface\n"
             "module child(I i);\n"
             "endmodule\n"
             "module top;\n"
             "  I inst();\n"
             "  child u(inst.A);\n"
             "endmodule\n"));
}

}  // namespace
