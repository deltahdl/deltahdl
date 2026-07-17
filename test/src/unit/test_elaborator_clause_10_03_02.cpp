#include "fixture_elaborator.h"

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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
