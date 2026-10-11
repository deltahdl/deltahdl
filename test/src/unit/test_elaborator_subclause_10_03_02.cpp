#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

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
  // §10.3.2 restates the one-continuous-assignment rule and refers to §6.5,
  // which states it in full, so the report carries §6.5.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "multiple continuous assignments to 'v'", 4,
                            "6.5"));
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
      "a continuous assignment to a net of a user-defined nettype drives the "
      "whole net and cannot index or select into it",
      4, "10.3.2"));
}

// The rule forbids indexing into or selecting from the nettype value. A
// bit-select is the indexing form; a part-select of a vector nettype is the
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
      "a continuous assignment to a net of a user-defined nettype drives the "
      "whole net and cannot index or select into it",
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
      "a continuous assignment to a net of a user-defined nettype drives the "
      "whole net and cannot index or select into it",
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'v' has both an initializer and a continuous", 3, "10.3.2"));
}

// §10.3.2 with A.8.3 (printed page 1210): a continuous assignment's net lvalue
// takes a constant_select, and a constant_part_select_range includes the
// constant_indexed_range `constant_expression +: constant_expression` and its
// `-:` form, so an indexed part-select whose base and width are constant --
// literals, or a parameter -- is a target like `a[3:0]`.
TEST(ContAssignStatementElaboration,
     ConstantIndexedPartSelectTargetsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  parameter P = 5;\n"
      "  tri [7:0] a, b;\n"
      "  assign a[1 -: 4] = 4'b0011;\n"
      "  assign b[P +: 2] = 2'b10;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.3.2: an indexed part-select whose base is a variable is no
// constant_indexed_range, so as a continuous assignment's target it is still
// reported under the subclause.
TEST(ContAssignStatementElaboration,
     VariableBaseIndexedPartSelectTargetErrors) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic [2:0] i;\n"
      "  tri [7:0] c;\n"
      "  assign c[i +: 2] = 2'b11;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "continuous assignment left-hand side requires a "
                            "constant select expression",
                            4, "10.3.2"));
}

// Table 10-1: every select on a continuous assignment's left-hand side is
// constant, the selects beneath the outermost one and those under a member
// access included.
TEST(ContAssignStatementElaboration, NestedNonConstantSelectErrors) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic [1:0] i;\n"
      "  wire [3:0] w [4];\n"
      "  assign w[i][0] = 1'b1;\n"
      "  assign w[0][i -: 1] = 1'b1;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4u, 5u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "continuous assignment left-hand side requires "
                              "a constant select expression",
                              line, "10.3.2"));
  }
}

// Syntax 10-1 gives the continuous assignment to variables no drive strength
// and a delay_control rather than a delay3, whether the target names the
// variable whole, through a select or as a concatenation element.
TEST(ContAssignStatementElaboration, StrengthAndDelay3OnVariableSelectErrors) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic [3:0] v; logic a, b;\n"
      "  assign (strong0, weak1) v[0] = a;\n"
      "  assign #(1,2) v[1] = a;\n"
      "  assign #(1,2) {b, v[2]} = 2'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength not allowed on continuous "
                            "assignment to a variable",
                            3, "10.3.4"));
  for (uint32_t line : {4u, 5u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "multiple delays not allowed on continuous "
                              "assignment to a variable",
                              line, "10.3.3"));
  }
}

// §10.3.2: a variable a continuous assignment writes, through a select or as a
// concatenation element, takes no initializer, and one written whole as an
// element takes no procedural assignment and no second continuous one.
TEST(ContAssignStatementElaboration, SelectAndConcatenationTargetsAreDrivers) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic a, b, c, x;\n"
      "  logic [3:0] v = 4'h0;\n"
      "  assign v[0] = x;\n"
      "  assign {a, b} = 2'b10;\n"
      "  assign {c, a} = 2'b01;\n"
      "  initial b = 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'v' has both an initializer and a "
                            "continuous assignment",
                            4, "10.3.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "multiple continuous assignments to 'a'", 6,
                            "6.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'b' has both continuous and procedural "
                            "assignments",
                            5, "6.5"));
}

// §10.3.2: a variable may be driven by one primitive output as by one
// continuous assignment, so one a gate drives takes no initializer, no
// procedural assignment and no second driver; an n-output gate drives every
// terminal but its last.
TEST(ContAssignStatementElaboration, PrimitiveOutputIsVariableDriver) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic x, y, z, u, v;\n"
      "  logic w = 1'b0;\n"
      "  buf g1(y, z, x);\n"
      "  initial y = 0;\n"
      "  assign z = 1'b1;\n"
      "  and g2(w, x, x);\n"
      "  not g3(u, x);\n"
      "  not g4(u, v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'y' has both continuous and procedural "
                            "assignments",
                            4, "6.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "multiple continuous assignments to 'z'", 6,
                            "6.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'w' has both an initializer and a "
                            "primitive output driving it",
                            7, "10.3.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'u' is driven by more than one "
                            "continuous assignment or primitive output",
                            9, "10.3.2"));
}

// §10.3.2: an element of an array of nets of a user-defined nettype is itself
// a whole net, which a continuous assignment may drive.
TEST(ContAssignStatementElaboration, NettypeArrayElementTargetSucceeds) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  nettype logic T;\n"
      "  T n[3];\n"
      "  assign n[1] = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.3.2: a select beyond the array's unpacked dimensions selects into the
// nettype's data type, however deeply the selects nest.
TEST(ContAssignStatementElaboration, NettypeArrayElementSelectErrors) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  nettype logic [1:0] T2;\n"
      "  T2 p[2];\n"
      "  assign p[1][0] = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a continuous assignment to a net of a user-defined nettype drives the "
      "whole net and cannot index or select into it",
      4, "10.3.2"));
}

}  // namespace
