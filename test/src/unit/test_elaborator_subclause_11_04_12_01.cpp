#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "helpers_eval_op.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ReplicationElaboration, ReplicationInContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [1:0] x;\n"
      "  assign a = {4{x}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ReplicationElaboration, ReplicationInInitialBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [1:0] x;\n"
      "  initial a = {4{x}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ReplicationElaboration, ConstantReplicationInParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter [31:0] P = {4{8'hFF}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ReplicationElaboration, ReplicationOnLhsOfBlockingAssign) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  initial {4{a}} = 8'hFF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication shall not appear on the left-hand "
                            "side of an assignment",
                            3, "11.4.12.1"));
}

TEST(ReplicationElaboration, ReplicationOnLhsOfNonblockingAssign) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  initial {4{a}} <= 8'hFF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication shall not appear on the left-hand "
                            "side of an assignment",
                            3, "11.4.12.1"));
}

TEST(ReplicationElaboration, ReplicationOnLhsOfContAssign) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  assign {4{a}} = 8'hFF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication shall not appear on the left-hand "
                            "side of an assignment",
                            3, "11.4.12.1"));
}

TEST(ReplicationElaboration, ReplicationInsideLhsConcat) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  logic [3:0] b;\n"
      "  initial {b, {2{a}}} = 8'hFF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication shall not appear on the left-hand "
                            "side of an assignment",
                            4, "11.4.12.1"));
}

TEST(ReplicationElaboration, ReplicationOnOutputPort) {
  ElabFixture f;
  ElaborateSrc(
      "module child(output [7:0] o);\n"
      "  assign o = 8'hAA;\n"
      "endmodule\n"
      "module m;\n"
      "  logic [1:0] a;\n"
      "  child u(.o({4{a}}));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication shall not appear in an output or "
                            "inout port connection",
                            6, "11.4.12.1"));
}

TEST(ReplicationElaboration, ReplicationOnInoutPort) {
  ElabFixture f;
  ElaborateSrc(
      "module child(inout [7:0] io);\n"
      "endmodule\n"
      "module m;\n"
      "  logic [1:0] a;\n"
      "  child u(.io({4{a}}));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication shall not appear in an output or "
                            "inout port connection",
                            5, "11.4.12.1"));
}

TEST(ReplicationElaboration, ReplicationOnInputPortOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input [7:0] i);\n"
      "endmodule\n"
      "module m;\n"
      "  logic [1:0] a;\n"
      "  child u(.i({4{a}}));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ReplicationElaboration, XMultiplierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = {1'bx{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            3, "11.4.12.1"));
}

TEST(ReplicationElaboration, ZMultiplierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = {1'bz{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            3, "11.4.12.1"));
}

TEST(ReplicationElaboration, ZeroReplicationStandaloneRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  initial result = {0{a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "zero replication shall appear only within a concatenation "
                    "in which at least one operand has a positive size",
                    4, "11.4.12.1"));
}

TEST(ReplicationElaboration, ZeroReplicationInsideConcatOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  logic [3:0] result;\n"
      "  initial result = {a, {0{b}}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.12.1: a zero-multiplier replication is only allowed inside a
// concatenation that has at least one positive-size operand. A concatenation
// built entirely from zero replications has no such operand and is rejected.
TEST(ReplicationElaboration, ZeroReplicationConcatAllZeroRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  logic [3:0] result;\n"
      "  initial result = {{0{a}}, {0{b}}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "zero replication shall appear only within a concatenation "
                    "in which at least one operand has a positive size",
                    4, "11.4.12.1"));
}

TEST(ReplicationElaboration, NegativeMultiplierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = {-1{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not be negative", 3,
                            "11.4.12.1"));
}

// §11.4.12.1: the multiplier is a constant expression, so the standalone-zero
// rule applies to a parameter that evaluates to zero, not only a literal zero.
// The zero here comes from a `parameter` (§11.2.1) resolved at elaboration, and
// the replication stands alone (not inside a concatenation with a positive-size
// operand), so it is rejected.
TEST(ReplicationElaboration, ParameterZeroMultiplierStandaloneRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter Z = 0;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  initial result = {Z{a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "zero replication shall appear only within a concatenation "
                    "in which at least one operand has a positive size",
                    5, "11.4.12.1"));
}

// §11.4.12.1: a negative multiplier is illegal even when it comes from a
// parameter (§11.2.1) rather than a literal; the constant-expression evaluation
// resolves the parameter in the module scope and rejects the negative value.
TEST(ReplicationElaboration, ParameterNegativeMultiplierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter Z = -1;\n"
      "  logic [7:0] a;\n"
      "  initial a = {Z{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not be negative", 4,
                            "11.4.12.1"));
}

}  // namespace
