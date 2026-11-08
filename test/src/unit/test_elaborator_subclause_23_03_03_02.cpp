#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(PortConnectionRulesForVariablesElaboration,
     InputPortConnectsToExpression) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("module child(input logic [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] x;\n"
             "  child u(.a(x + 8'd1));\n"
             "endmodule\n",
             f));
}

TEST(PortConnectionRulesForVariablesElaboration, UnconnectedInputPortNoError) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("module child(input logic [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  child u();\n"
             "endmodule\n",
             f));
}

TEST(PortConnectionRulesForVariablesElaboration,
     InputPortVarWithContAssignErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input var logic a);\n"
      "  assign a = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'a' is declared as an input port and "
                            "cannot be the target of an assignment",
                            2, "23.3.3.2"));
}

TEST(PortConnectionRulesForVariablesElaboration,
     InputPortVarWithProceduralAssignErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input var logic a);\n"
      "  initial a = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'a' is declared as an input port and "
                            "cannot be the target of an assignment",
                            2, "23.3.3.2"));
}

TEST(PortConnectionRulesForVariablesElaboration,
     InputPortDrivenFromAlwaysCombIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input var logic a);\n"
      "  always_comb a = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'a' is declared as an input port and "
                            "cannot be the target of an assignment",
                            2, "23.3.3.2"));
}

TEST(PortConnectionRulesForVariablesElaboration, OutputPortConnectsToVariable) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("module child(output logic [7:0] y);\n"
             "  assign y = 8'hAB;\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] result;\n"
             "  child u(.y(result));\n"
             "endmodule\n",
             f));
}

TEST(PortConnectionRulesForVariablesElaboration,
     VarOutputPortAndContAssignErrors) {
  ElabFixture f;
  Elaborate(
      "module child(output logic y);\n"
      "endmodule\n"
      "module t;\n"
      "  logic v;\n"
      "  child c(.y(v));\n"
      "  assign v = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'v' driven by both output port and "
                            "continuous assignment",
                            5, "6.5"));
}

TEST(PortConnectionRulesForVariablesElaboration,
     VarOutputPortWithProceduralErrors) {
  ElabFixture f;
  Elaborate(
      "module child(output logic y);\n"
      "endmodule\n"
      "module t;\n"
      "  logic v;\n"
      "  child c(.y(v));\n"
      "  initial v = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'v' driven by output port has "
                            "procedural assignments",
                            5, "6.5"));
}

TEST(PortConnectionRulesForVariablesElaboration,
     VarOutputPortWithInitializerErrors) {
  ElabFixture f;
  Elaborate(
      "module child(output logic y);\n"
      "endmodule\n"
      "module t;\n"
      "  logic v = 1'b0;\n"
      "  child c(.y(v));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'v' driven by output port has an "
                            "initializer",
                            5, "6.5"));
}

TEST(PortConnectionRulesForVariablesElaboration,
     NetOutputPortAndContAssignAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module child(output logic y);\n"
      "endmodule\n"
      "module t;\n"
      "  wire w;\n"
      "  child c(.y(w));\n"
      "  assign w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PortConnectionRulesForVariablesElaboration,
     OutputPortConcatVariableElementDoubleDriveErrors) {
  ElabFixture f;
  Elaborate(
      "module child(output logic [3:0] y);\n"
      "  assign y = 4'h5;\n"
      "endmodule\n"
      "module t;\n"
      "  logic a, b, c, d;\n"
      "  child u(.y({a, b, c, d}));\n"
      "  assign a = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'a' driven by both output port and "
                            "continuous assignment",
                            6, "6.5"));
}

TEST(PortConnectionRulesForVariablesElaboration,
     OutputPortConcatNetElementAllowsExtraDriver) {
  ElabFixture f;
  auto* design = Elaborate(
      "module child(output logic [3:0] y);\n"
      "  assign y = 4'h5;\n"
      "endmodule\n"
      "module t;\n"
      "  wire w0, w1, w2, w3;\n"
      "  child u(.y({w0, w1, w2, w3}));\n"
      "  assign w0 = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PortConnectionRulesForVariablesElaboration,
     OutputPortConcatVariableDrivenByTwoOutputsErrors) {
  ElabFixture f;
  Elaborate(
      "module child(output logic [1:0] y);\n"
      "  assign y = 2'b0;\n"
      "endmodule\n"
      "module t;\n"
      "  logic a, b;\n"
      "  child u1(.y({a, b}));\n"
      "  child u2(.y({b, a}));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'a' driven by multiple outputs", 7,
                            "23.3.3.2"));
}

TEST(PortConnectionRulesForVariablesElaboration,
     OutputPortConnectsToVariableConcatenation) {
  ElabFixture f;
  auto* design = Elaborate(
      "module child(output logic [3:0] y);\n"
      "  assign y = 4'h5;\n"
      "endmodule\n"
      "module t;\n"
      "  logic a, b, c, d;\n"
      "  child u(.y({a, b, c, d}));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PortConnectionRulesForVariablesElaboration,
     InoutPortWithVarKeywordErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(inout var logic [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable data type is not permitted on inout "
                            "port 'a'",
                            1, "23.3.3.2"));
}

TEST(PortConnectionRulesForVariablesElaboration,
     VariableConnectedToInoutPortErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(inout logic w);\n"
      "endmodule\n"
      "module top;\n"
      "  logic v;\n"
      "  child u(.w(v));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'v' cannot be connected to inout "
                            "port 'w'",
                            5, "23.3.3.3"));
}

TEST(PortConnectionRulesForVariablesElaboration,
     RefPortBindingHasRefDirection) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(ref logic [7:0] v);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  child u(.v(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 1u);
  EXPECT_EQ(bindings[0].direction, Direction::kRef);
}

TEST(PortConnectionRulesForVariablesElaboration, RefPortConnectedToNetErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(ref logic [7:0] v);\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] w;\n"
      "  child u(.v(w));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net 'w' cannot be connected to ref port 'v'", 5,
                            "23.3.3.2"));
}

TEST(PortConnectionRulesForVariablesElaboration, RefPortLeftUnconnectedErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(ref logic [7:0] v);\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref port 'v' of module 'child' cannot be left "
                            "unconnected",
                            4, "23.3.3.2"));
}

TEST(PortConnectionRulesForVariablesElaboration,
     RefPortConnectedToNonEquivalentVariableErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(ref logic [7:0] v);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [3:0] x;\n"
      "  child u(.v(x));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "ref port 'v' requires an equivalent variable data type", 5, "23.3.3.2"));
}

TEST(PortConnectionRulesForVariablesElaboration,
     PortVariableToInterconnectNetErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(output logic y);\n"
      "  assign y = 1'b0;\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.y(ic));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "port variable 'y' cannot be connected to "
                            "interconnect 'ic'",
                            6, "23.3.3.2"));
}

TEST(PortConnectionRulesForVariablesElaboration,
     PortVariableToInterconnectPortErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input var logic a);\n"
      "endmodule\n"
      "module mid(interconnect ic);\n"
      "  child u(.a(ic));\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect w;\n"
      "  mid m(.ic(w));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "port variable 'a' cannot be connected to "
                            "interconnect 'ic'",
                            4, "23.3.3.2"));
}

TEST(PortConnectionRulesForVariablesElaboration,
     RefConnectionMayBeInitializedAndAssignedProcedurally) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("module child(ref int r);\n"
             "  initial #1 r = 1;\n"
             "endmodule\n"
             "module top;\n"
             "  int v = 10;\n"
             "  child c(.r(v));\n"
             "  initial #2 v = 20;\n"
             "endmodule\n",
             f));
}

}  // namespace
