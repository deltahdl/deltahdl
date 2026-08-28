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

// §11.4.12.1 says a replication "shall not appear on the left-hand side of an
// assignment", a rule about the lvalue and not about the statement the
// assignment stands in.
//
// ElaboratorOperationRules::WalkStmtsForReplicateLvalue in
// src/elaborator/elaborator_validate_operations_arrays.cpp reached six of the
// thirteen statement links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states. The seven cases here
// each put `{4{a}} = 8'hFF` in one of the seven positions it did not read,
// where the lvalue reached CheckReplicateLvalue not at all.
//
// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword [ :
// block_identifier ]`, so a fork arm is a statement position like any other.
TEST(ReplicationElaboration, ReplicationOnLvalueInAForkArmNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  initial begin\n"
      "    fork\n"
      "      {4{a}} = 8'hFF;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication shall not appear on the left-hand", 5,
                            "11.4.12.1"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case covers
// the pass arm and the one below it the fail arm.
TEST(ReplicationElaboration,
     ReplicationOnLvalueInAnAssertionPassStatementNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  logic ok;\n"
      "  initial assert (ok) {4{a}} = 8'hFF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication shall not appear on the left-hand", 4,
                            "11.4.12.1"));
}

TEST(ReplicationElaboration,
     ReplicationOnLvalueInAnAssertionFailStatementNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  logic ok;\n"
      "  initial assert (ok) else {4{a}} = 8'hFF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication shall not appear on the left-hand", 4,
                            "11.4.12.1"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. The rule
// is a static one, so it holds whether the weighted draw would select the item
// or not.
TEST(ReplicationElaboration, ReplicationOnLvalueInARandcaseItemNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  initial randcase 1: {4{a}} = 8'hFF; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication shall not appear on the left-hand", 3,
                            "11.4.12.1"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions.
TEST(ReplicationElaboration,
     ReplicationOnLvalueInARandsequenceCodeBlockNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { {4{a}} = 8'hFF; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication shall not appear on the left-hand", 5,
                            "11.4.12.1"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments |
// for_variable_declaration { , for_variable_declaration }` and
// `for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call`. A.6.2 gives `variable_assignment ::=
// variable_lvalue = expression` and `operator_assignment ::= variable_lvalue
// assignment_operator expression`, whose assignment_operator includes `=`, so
// an assignment stands at each of the two positions: this case writes one at
// the initialization and the case below it writes one at the step.
TEST(ReplicationElaboration,
     ReplicationOnLvalueInAForLoopInitializationNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  int i;\n"
      "  initial for ({4{a}} = 8'hFF; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication shall not appear on the left-hand", 4,
                            "11.4.12.1"));
}

TEST(ReplicationElaboration, ReplicationOnLvalueInAForLoopStepNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; {4{a}} = 8'hFF) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication shall not appear on the left-hand", 4,
                            "11.4.12.1"));
}

// §11.4.12.1 allows a zero replication only inside a concatenation in which at
// least one operand has a positive size, and says nothing about the statement
// the replication is written in.
//
// WalkStmtsForZeroReplicateStandalone in
// src/elaborator/elaborator_validate_operations_arrays.cpp reached six of the
// thirteen statement links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states. The seven cases here
// each put `result = {0{a}}` in one of the seven positions it did not read,
// every one of which elaborated clean beforehand.
//
// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword [ :
// block_identifier ]`, so a fork arm is a statement position like any other.
TEST(ReplicationElaboration,
     ZeroReplicationStandaloneInAForkArmNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  initial begin\n"
      "    fork\n"
      "      result = {0{a}};\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "zero replication shall appear only within a", 6,
                            "11.4.12.1"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case covers
// the pass arm and the one below it the fail arm.
TEST(ReplicationElaboration,
     ZeroReplicationStandaloneInAnAssertionPassStatementNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  logic ok;\n"
      "  initial assert (ok) result = {0{a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "zero replication shall appear only within a", 5,
                            "11.4.12.1"));
}

TEST(ReplicationElaboration,
     ZeroReplicationStandaloneInAnAssertionFailStatementNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  logic ok;\n"
      "  initial assert (ok) else result = {0{a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "zero replication shall appear only within a", 5,
                            "11.4.12.1"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. The rule
// is a static one, so it holds whether the weighted draw would select the item
// or not.
TEST(ReplicationElaboration,
     ZeroReplicationStandaloneInARandcaseItemNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  initial randcase 1: result = {0{a}}; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "zero replication shall appear only within a", 4,
                            "11.4.12.1"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions.
TEST(ReplicationElaboration,
     ZeroReplicationStandaloneInARandsequenceCodeBlockNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { result = {0{a}}; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "zero replication shall appear only within a", 6,
                            "11.4.12.1"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments |
// for_variable_declaration { , for_variable_declaration }` and
// `for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call`. A.6.2 gives `variable_assignment ::=
// variable_lvalue = expression` and `operator_assignment ::= variable_lvalue
// assignment_operator expression`, whose assignment_operator includes `=`, so
// an assignment stands at each of the two positions: this case writes one at
// the initialization and the case below it writes one at the step.
TEST(ReplicationElaboration,
     ZeroReplicationStandaloneInAForLoopInitializationNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  int i;\n"
      "  initial for (result = {0{a}}; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "zero replication shall appear only within a", 5,
                            "11.4.12.1"));
}

TEST(ReplicationElaboration,
     ZeroReplicationStandaloneInAForLoopStepNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; result = {0{a}}) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "zero replication shall appear only within a", 5,
                            "11.4.12.1"));
}

// §11.4.12.1 requires a replication multiplier to be a constant expression that
// contains no x or z, a rule about the multiplier and not about the statement
// around it.
//
// ElaboratorOperationRules::WalkStmtsForReplicateMultiplier in
// src/elaborator/elaborator_validate_operations_arrays.cpp reached six of the
// thirteen statement links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states. The seven cases here
// each put `a = {1'bx{1'b0}}` in one of the seven positions it did not read,
// where the multiplier reached CheckReplicateRepeatCount not at all.
//
// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword [ :
// block_identifier ]`, so a fork arm is a statement position like any other.
TEST(ReplicationElaboration, XMultiplierInAForkArmNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = {1'bx{1'b0}};\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            5, "11.4.12.1"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case covers
// the pass arm and the one below it the fail arm.
TEST(ReplicationElaboration,
     XMultiplierInAnAssertionPassStatementNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic ok;\n"
      "  initial assert (ok) a = {1'bx{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            4, "11.4.12.1"));
}

TEST(ReplicationElaboration,
     XMultiplierInAnAssertionFailStatementNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic ok;\n"
      "  initial assert (ok) else a = {1'bx{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            4, "11.4.12.1"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. The rule
// is a static one, so it holds whether the weighted draw would select the item
// or not.
TEST(ReplicationElaboration, XMultiplierInARandcaseItemNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial randcase 1: a = {1'bx{1'b0}}; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            3, "11.4.12.1"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions.
TEST(ReplicationElaboration,
     XMultiplierInARandsequenceCodeBlockNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { a = {1'bx{1'b0}}; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            5, "11.4.12.1"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments |
// for_variable_declaration { , for_variable_declaration }` and
// `for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call`. A.6.2 gives `variable_assignment ::=
// variable_lvalue = expression` and `operator_assignment ::= variable_lvalue
// assignment_operator expression`, whose assignment_operator includes `=`, so
// an assignment stands at each of the two positions: this case writes one at
// the initialization and the case below it writes one at the step.
TEST(ReplicationElaboration,
     XMultiplierInAForLoopInitializationNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  int i;\n"
      "  initial for (a = {1'bx{1'b0}}; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            4, "11.4.12.1"));
}

TEST(ReplicationElaboration, XMultiplierInAForLoopStepNames11_4_12_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; a = {1'bx{1'b0}}) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            4, "11.4.12.1"));
}

}  // namespace
