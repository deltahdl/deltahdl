#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;
namespace {

TEST(ForceReleaseElaboration, VarLvalueForceReleaseElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial begin force x = 1; release x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  initial begin force w = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceConcatLhsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin force {a, b} = 2'b11; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceConstBitSelectNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force bus[3] = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceConstPartSelectNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force bus[7:4] = 4'hF; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceBitSelectVariableLhsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  initial begin force data[3] = 1'b1; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select of a variable is not a legal force LHS", 3,
      "10.6.2"));
}

TEST(ForceReleaseElaboration, ForcePartSelectVariableLhsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  initial begin force data[3:0] = 4'hA; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select of a variable is not a legal force LHS", 3,
      "10.6.2"));
}

TEST(ForceReleaseElaboration, ForceBitSelectUserNettypeNetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  nettype logic [7:0] my_t;\n"
      "  my_t bus;\n"
      "  initial begin force bus[3] = 1'b1; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nettype is not a legal force LHS", 4, "10.6.2"));
}

TEST(ForceReleaseElaboration, ForcePartSelectUserNettypeNetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  nettype logic [7:0] my_t;\n"
      "  my_t bus;\n"
      "  initial begin force bus[7:4] = 4'hF; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nettype is not a legal force LHS", 4, "10.6.2"));
}

// §10.6.2 (printed page 257): "A force or release statement shall not be
// applied to a variable that is being assigned by a mixture of continuous and
// procedural assignments." §6.5 rejects the mixture itself and its report
// stands at the continuous assignment on line 3, so naming that report proves
// nothing about the force; this names §10.6.2's own, at the force on line 6.
TEST(ForceReleaseElaboration, ForceOnAMixedAssignmentVariableNamesItsOwnRule) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "  initial begin\n"
      "    x = 1'b1;\n"
      "    force x = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "force or release applied to variable 'x'", 6,
                            "10.6.2"));
}

TEST(ForceReleaseElaboration,
     ForceOnAVariableWithOnlyAContinuousAssignmentIsAccepted) {
  // §6.5 (printed page 91): "A force statement is neither a continuous nor a
  // procedural assignment." So a lone force beside a continuous assignment is
  // no mixture, and this is what stops the rule from rejecting every force on a
  // continuously assigned variable.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "  initial force x = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration,
     ForceOnAVariableWithOnlyProceduralAssignmentsIsAccepted) {
  // The other edge of the same rule: procedural assignments alone are no
  // mixture either, so the force stands.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    x = 1'b0;\n"
      "    force x = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceConcatWithBitSelectVariableIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  wire w;\n"
      "  initial begin force {w, data[0]} = 2'b11; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select of a variable is not a legal force LHS", 4,
      "10.6.2"));
}

// §10.6.2 admits a constant bit-select of a vector net as a force target, and a
// constant expression per §11.2.1 is not only a literal but also a parameter.
// A parameter-indexed net bit-select is therefore a legal force LHS.
TEST(ForceReleaseElaboration, ForceParamBitSelectNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = 3;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force bus[P] = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A localparam is another §11.2.1 constant form, so a localparam-bounded
// part-select of a vector net is likewise a legal force LHS.
TEST(ForceReleaseElaboration, ForceLocalparamPartSelectNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam HI = 7;\n"
      "  localparam LO = 4;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force bus[HI:LO] = 4'hF; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The concatenation form admits any of the individual legal LHS elements. A
// concatenation mixing a whole net with a constant bit-select of a vector net
// is accepted, exercising the accept path through the concatenation recursion.
TEST(ForceReleaseElaboration, ForceConcatWithNetBitSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force {w, bus[3]} = 2'b11; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.6.2 names both statements, so a check reading only StmtKind::kForce
// leaves this red while the force case above passes.
TEST(ForceReleaseElaboration,
     ReleaseOnAMixedAssignmentVariableNamesItsOwnRule) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "  initial begin\n"
      "    x = 1'b1;\n"
      "    release x;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "force or release applied to variable 'x'", 6,
                            "10.6.2"));
}

// §10.6.2's rule on what a force may name is decided by the expression, not by
// where the statement stands, and §18.16 makes each randcase_item's body a
// statement_or_null. ForceBitSelectVariableLhsIsError above writes the same
// force in a begin-end block and expects the same report.
TEST(ForceReleaseElaboration, ForceBitSelectVariableLhsInARandcaseArmIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  initial randcase\n"
      "    1 : force data[3] = 1'b1;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select of a variable is not a legal force LHS", 4,
      "10.6.2"));
}

// The regression against a walk that reports on every force it newly reaches:
// forcing a whole variable in a randcase arm is what §10.6.2 allows.
TEST(ForceReleaseElaboration, ForceOfAWholeVariableInARandcaseArmIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  initial randcase\n"
      "    1 : force data = 8'hFF;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a force in a randsequence production's code block is the same force
// ForceBitSelectVariableLhsIsError above writes in a begin-end block, and
// §10.6.2 rules on it the same way.
TEST(ForceReleaseElaboration, ForceBitSelectVariableLhsInARandsequenceIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { force data[3] = 1'b1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bit-select or part-select of a variable is not a legal force LHS", 5,
      "10.6.2"));
}

// §10.6.2's rule against forcing a variable assigned by both a continuous and
// a procedural assignment holds wherever the force stands, and §18.16 makes
// each randcase_item's body a statement_or_null.
// ForceOnAMixedAssignmentVariableNamesItsOwnRule above writes the same force in
// a begin-end block and expects the same report.
TEST(ForceReleaseElaboration,
     ForceInARandcaseArmOverAMixedlyAssignedVariableIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "  initial begin\n"
      "    x = 1'b1;\n"
      "    randcase\n"
      "      1 : force x = 1'b1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "force or release applied to variable 'x'", 7,
                            "10.6.2"));
}

}  // namespace
