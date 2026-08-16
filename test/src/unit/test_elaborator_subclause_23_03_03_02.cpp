
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

// §9.2.2.2 makes always_comb a structured procedure exactly as §9.2.2.1 makes
// always one, and neither narrows what its body may assign, so the §23.3.3.2
// rule that a variable input port is not the target of an assignment is the
// same rule here as in the initial case above. The procedure keyword is the
// only thing this case varies, because that is what decides whether the
// assignment is collected as a procedural one at all.
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
  // The implied continuous assignment of §23.3.3.2 collides with the explicit
  // one under the §6.5 single-continuous-driver rule, which is what reports.
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
  // §6.5 is the rule reported: the implied continuous assignment of §23.3.3.2
  // and a procedural assignment cannot both drive the variable.
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
  // §6.5 is the rule reported: the initializer is a second driver on the
  // variable the §23.3.3.2 implied continuous assignment already drives.
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

// §23.3.3.2 admits an output port connected to a concatenation of variables,
// not only a single variable. The implied continuous assignment drives each
// variable element, so an additional continuous assignment to any element is
// illegal just as it is for the single-variable form.
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
  // The collision between the implied continuous assignment and the explicit
  // one is reported under §6.5, at the instantiation that implies the driver.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'a' driven by both output port and "
                            "continuous assignment",
                            6, "6.5"));
}

// A net element inside a concatenation connected to an output port keeps the
// §23.3.3.3 net rule: multiple drivers are permitted, so an extra continuous
// assignment to that net element is legal.
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

// A variable element that is driven by the output ports of two separate
// instances is driven by multiple outputs, which is illegal regardless of the
// concatenation wrapping.
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

// R2a admits a concatenation of variables as the output-port connection, not
// only a single variable. With no other driver on any element, the connection
// is legal -- the accepting counterpart to the concat double-drive rejections.
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
  // §23.2.2.3 makes `inout logic w` a net, so the rule reported for the
  // variable connection is §23.3.3.3's rather than §23.3.3.2's.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'v' cannot be connected to inout "
                            "port 'w'",
                            5, "23.3.3.3"));
}

// A ref port connected to an equivalent variable binds with ref direction and
// is accepted -- the latter also guarding that the equivalence gate does not
// reject a matching-width, matching-type variable connection.
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

// §23.3.3.2 requires a ref port to be connected to an *equivalent* variable
// data type, not merely an assignment-compatible one. A variable whose packed
// width differs from the ref port is not equivalent and shall be rejected --
// distinct from the net-connection rejection above.
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

}  // namespace
