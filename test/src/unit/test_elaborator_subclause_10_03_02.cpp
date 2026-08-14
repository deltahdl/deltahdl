#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ContAssignStatementElaboration, MultipleContAssigns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  assign a = b, c = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 2u);
}

TEST(ContAssignStatementElaboration, VarWithInitializerAndContAssignErrors) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic v = 1'b0;\n"
      "  assign v = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'v' has both an initializer and a continuous assignment", 3,
      "10.3.2"));
}

TEST(ContAssignStatementElaboration,
     VarWithoutInitializerAndContAssignSucceeds) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic v;\n"
      "  assign v = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ContAssignStatementElaboration, NetAllowsMultipleContAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b0;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ContAssignStatementElaboration, VarMultipleContAssignsErrors) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic v;\n"
      "  assign v = 1'b0;\n"
      "  assign v = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "multiple continuous assignments to 'v'", 4,
                            "10.3.2"));
}

TEST(ContAssignStatementElaboration, NettypeLhsWithSelectErrors) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  nettype logic mytype;\n"
      "  mytype n;\n"
      "  assign n[0] = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "continuous assignment to a nettype net shall not contain indexing or "
      "select",
      4, "10.3.2"));
}

// The rule forbids "indexing or select operations" into the nettype value.
// A bit-select is the indexing form; a part-select of a vector nettype is the
// distinct select form and must be rejected the same way, since a continuous
// assignment to a nettype net must drive the entire nettype value.
TEST(ContAssignStatementElaboration, NettypeLhsWithPartSelectErrors) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  nettype logic [7:0] mytype;\n"
      "  mytype n;\n"
      "  assign n[3:0] = 4'h0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "continuous assignment to a nettype net shall not contain indexing or "
      "select",
      4, "10.3.2"));
}

TEST(ContAssignStatementElaboration, NettypeLhsWithoutSelectSucceeds) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  nettype logic mytype;\n"
      "  mytype n;\n"
      "  assign n = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The target net of a continuous assignment need not be declared explicitly:
// an undeclared left-hand identifier inherits an implicit net declaration
// (§6.10). Building the input from that real form — a bare name never declared
// — and elaborating it must succeed, with the implicit net standing in as the
// continuous assignment's driven net.
TEST(ContAssignStatementElaboration,
     ContAssignToImplicitlyDeclaredNetSucceeds) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ContAssignStatementElaboration, VarContAndProceduralAssignErrors) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic v;\n"
      "  assign v = 1'b0;\n"
      "  initial v = 1'b1;\n"
      "endmodule\n",
      f);
  // Elaborator::ValidateMixedAssignments reports a whole-variable mix of a
  // continuous and a procedural driver under §6.5, at the continuous
  // assignment's location.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'v' has both continuous and procedural assignments", 3, "6.5"));
}

TEST(ContAssignStatementElaboration, ModuleWithContinuousAssignElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->assigns.empty());
}

TEST(ContAssignStatementElaboration, ContAssignInInterfaceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  logic a;\n"
      "  wire b;\n"
      "  assign b = a;\n"
      "endinterface\n",
      f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ContAssignStatementElaboration, VarContAssignAndNonblockingErrors) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic v;\n"
      "  assign v = 1'b0;\n"
      "  always @(*) v <= 1'b1;\n"
      "endmodule\n",
      f);
  // Elaborator::ValidateMixedAssignments reports a whole-variable mix of a
  // continuous and a procedural driver under §6.5, at the continuous
  // assignment's location.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'v' has both continuous and procedural assignments", 3, "6.5"));
}

TEST(ContAssignStatementElaboration, NetDeclAssignAndContAssignAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w = 1'b0;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Unlike a variable, a net may be driven by a mixture of drivers — here a
// module output and a continuous assignment together — without error.
TEST(ContAssignStatementElaboration, NetDrivenByOutputAndContAssignAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module child(output logic y);\n"
      "endmodule\n"
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b0;\n"
      "  child c(.y(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ContAssignStatementElaboration, NettypeLhsWithMemberAccessErrors) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  nettype logic mytype;\n"
      "  mytype n;\n"
      "  assign n.a = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "continuous assignment to a nettype net shall not contain indexing or "
      "select",
      4, "10.3.2"));
}

TEST(ContAssignStatementElaboration, VarMultipleOutputPortsErrors) {
  ElabFixture f;
  Elaborate(
      "module child(output logic y);\n"
      "endmodule\n"
      "module t;\n"
      "  logic v;\n"
      "  child c1(.y(v));\n"
      "  child c2(.y(v));\n"
      "endmodule\n",
      f);
  // Two output ports driving one variable is reported by
  // Elaborator::RecordOutputPortDrivenVariables under §23.3.3.2, at the second
  // instantiation.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'v' driven by multiple outputs", 6,
                            "23.3.3.2"));
}

TEST(ContAssignStatementElaboration, VarOutputPortWithInitializerErrors) {
  ElabFixture f;
  Elaborate(
      "module child(output logic y);\n"
      "endmodule\n"
      "module t;\n"
      "  logic v = 1'b0;\n"
      "  child c(.y(v));\n"
      "endmodule\n",
      f);
  // Elaborator::ValidateMixedAssignments reports the output-port driver
  // conflicts under §6.5, at the instantiation that drives the variable.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'v' driven by output port has an initializer", 5, "6.5"));
}

// A variable may have at most one driver: a module output and a continuous
// assignment targeting the same variable are two drivers, which is an error.
TEST(ContAssignStatementElaboration, VarContAssignAndOutputPortErrors) {
  ElabFixture f;
  Elaborate(
      "module child(output logic y);\n"
      "endmodule\n"
      "module t;\n"
      "  logic v;\n"
      "  assign v = 1'b0;\n"
      "  child c(.y(v));\n"
      "endmodule\n",
      f);
  // Elaborator::ValidateMixedAssignments reports the output-port driver
  // conflicts under §6.5, at the instantiation that drives the variable.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'v' driven by both output port and continuous assignment", 6,
      "6.5"));
}

// A variable driven by a module output may not also be the target of a
// procedural assignment. The blocking form is exercised here.
TEST(ContAssignStatementElaboration, VarOutputPortWithProceduralAssignErrors) {
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
  // Elaborator::ValidateMixedAssignments reports the output-port driver
  // conflicts under §6.5, at the instantiation that drives the variable.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'v' driven by output port has procedural assignments", 5,
      "6.5"));
}

// The prohibition on a second driver covers every procedural-assignment form,
// so an output-driven variable that is also the target of a nonblocking
// assignment is the same error as the blocking case above.
TEST(ContAssignStatementElaboration, VarOutputPortWithNonblockingErrors) {
  ElabFixture f;
  Elaborate(
      "module child(output logic y);\n"
      "endmodule\n"
      "module t;\n"
      "  logic v;\n"
      "  child c(.y(v));\n"
      "  always @(*) v <= 1'b1;\n"
      "endmodule\n",
      f);
  // Elaborator::ValidateMixedAssignments reports the output-port driver
  // conflicts under §6.5, at the instantiation that drives the variable.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'v' driven by output port has procedural assignments", 5,
      "6.5"));
}

// §10.3.2: the report that rejects a variable carrying both an initializer and
// a continuous assignment names the subclause stating the rule, so a caller
// learns which rule was enforced without matching the wording of the message.
TEST(ContAssignStatementElaboration, VarInitializerAndContAssignNames10_3_2) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic v = 1'b0;\n"
      "  assign v = 1'b1;\n"
      "endmodule\n",
      f);
  const Diagnostic* d =
      FindDiag(f, "variable 'v' has both an initializer and a continuous");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "10.3.2");
}

}  // namespace
