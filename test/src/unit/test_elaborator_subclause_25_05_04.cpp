#include <gtest/gtest.h>

#include <string>

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
             "  typedef logic [1:0] pair_t;\n"
             "  logic a, b;\n"
             "  modport mp(input .P(pair_t'{a, b}));\n"
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

void ExpectConstantRefused(const std::string& decl, const std::string& item,
                           const std::string& port) {
  ElabFixture f;
  ElaborateSrc("interface I #(parameter K = 3) ();\n" + decl + "  modport mp(" +
                   item +
                   ");\n"
                   "endinterface\n"
                   "module top;\n"
                   "  I inst();\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "port-id '" + port +
                                "' in modport 'mp' has a constant port "
                                "expression and cannot be declared as output "
                                "or inout",
                            3, "25.5.4"));
}

TEST(ModportExpressionElaboration, AnInoutLiteralPortExpressionIsRefused) {
  ExpectConstantRefused("  logic unused;\n", "inout .P(2)", "P");
}

TEST(ModportExpressionElaboration, AnInoutParameterPortExpressionIsRefused) {
  ExpectConstantRefused("  logic unused;\n", "inout .P(K)", "P");
}

TEST(ModportExpressionElaboration, AnOutputLocalparamPortExpressionIsRefused) {
  ExpectConstantRefused("  localparam L = 5;\n", "output .P(L)", "P");
}

TEST(ModportExpressionElaboration,
     AnInoutConstVariablePortExpressionIsRefused) {
  ExpectConstantRefused("  const int x = 1;\n", "inout .Q(x)", "Q");
}

constexpr const char* kNotAnLvalueMsg =
    "port-id 'P' in modport 'mp' has a port expression that is not an "
    "lvalue and cannot be declared as output or inout";

TEST(ModportExpressionElaboration,
     DISABLED_AnOutputOperatorResultPortExpressionIsRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  logic a, b;\n"
      "  modport mp(output .P(a + b));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotAnLvalueMsg, 3, "25.5.4"));
}

TEST(ModportExpressionElaboration,
     DISABLED_AnInoutConditionalPortExpressionIsRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  logic a, b;\n"
      "  modport mp(inout .P(a ? b : a));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotAnLvalueMsg, 3, "25.5.4"));
}

TEST(ModportExpressionElaboration,
     DISABLED_AnOutputFunctionCallPortExpressionIsRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  logic a;\n"
      "  function automatic logic inv(logic v); return ~v; endfunction\n"
      "  modport mp(output .P(inv(a)));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotAnLvalueMsg, 4, "25.5.4"));
}

TEST(ModportExpressionElaboration, AnInputOperatorResultPortExpressionIsLegal) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  logic a, b;\n"
             "  function automatic logic inv(logic v); return ~v; "
             "endfunction\n"
             "  modport mp(input .P(a + b), input .Q(a ? b : a), "
             "input .R(inv(a)));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

TEST(ModportExpressionElaboration,
     DISABLED_AnUntypedAssignmentPatternPortExpressionIsRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  logic a, b;\n"
      "  modport mp(input .P('{a, b}));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern without a type prefix outside "
                            "an assignment-like context",
                            3, "10.9"));
}

TEST(ModportExpressionElaboration, TwoSimplePortsOfOneNameAreRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  logic a, b;\n"
      "  modport mp(input a, output a);\n"
      "  modport ok(input a, output b);\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate port-id 'a' in modport 'mp'", 3,
                            "25.5.4"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "duplicate port-id 'a' in modport 'ok'", 4,
                             "25.5.4"));
}

TEST(ModportExpressionElaboration,
     DISABLED_AnExpressionPortNameIsNoMemberOfTheInstance) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  logic [7:0] r;\n"
      "  modport A(output .P(r[3:0]));\n"
      "endinterface\n"
      "module top;\n"
      "  I i1();\n"
      "  initial begin i1.r = 1; i1.P = 1; end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference 'i1.P' is unresolved: 'P' "
                            "is not declared in interface 'I'",
                            7, "23.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "hierarchical reference 'i1.r' is unresolved: 'r' "
                             "is not declared in interface 'I'",
                             7, "23.6"));
}

TEST(ModportExpressionElaboration,
     DISABLED_AnExpressionPortNameIsHiddenFromAnotherModport) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  logic [7:0] r;\n"
      "  modport A(output .P(r[3:0]));\n"
      "  modport B(output r);\n"
      "endinterface\n"
      "module MB(I.B i);\n"
      "  initial begin i.r = 1; i.P = 1; end\n"
      "endmodule\n"
      "module top;\n"
      "  I i1();\n"
      "  MB u(i1.B);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'P' is not accessible through modport 'B' of "
                            "interface 'I'",
                            7, "25.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "'r' is not accessible through modport 'B' of "
                             "interface 'I'",
                             7, "25.5"));
}

}  // namespace
