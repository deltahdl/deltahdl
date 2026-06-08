
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(PortConnectionRulesForVariablesElaboration,
     InputPortConnectsToExpression) {
  EXPECT_TRUE(
      ElabOk("module child(input logic [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] x;\n"
             "  child u(.a(x + 8'd1));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForVariablesElaboration,
     UnconnectedInputPortNoError) {
  EXPECT_TRUE(
      ElabOk("module child(input logic [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  child u();\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForVariablesElaboration,
     InputPortVarWithContAssignErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input var logic a);\n"
      "  assign a = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(PortConnectionRulesForVariablesElaboration,
     InputPortVarWithProceduralAssignErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input var logic a);\n"
      "  initial a = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(PortConnectionRulesForVariablesElaboration,
     OutputPortConnectsToVariable) {
  EXPECT_TRUE(
      ElabOk("module child(output logic [7:0] y);\n"
             "  assign y = 8'hAB;\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] result;\n"
             "  child u(.y(result));\n"
             "endmodule\n"));
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

TEST(PortConnectionRulesForVariablesElaboration, RefPortBindingHasRefDirection) {
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
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 1u);
  EXPECT_EQ(bindings[0].direction, Direction::kRef);
}

TEST(PortConnectionRulesForVariablesElaboration,
     RefPortConnectedToNetErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(ref logic [7:0] v);\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] w;\n"
      "  child u(.v(w));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(PortConnectionRulesForVariablesElaboration,
     RefPortLeftUnconnectedErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(ref logic [7:0] v);\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

}
