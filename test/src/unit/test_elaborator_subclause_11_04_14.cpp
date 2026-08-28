#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast.h"

using namespace delta;

namespace {

TEST(StreamingOperatorElaboration, StreamingAsAssignmentSource) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  initial dst = {>> {a, b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingOperatorElaboration, StreamingWithBitStreamCast) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial b = int'({<< byte {a}});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingOperatorElaboration, StreamingNestedInStreaming) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [15:0] b;\n"
      "  initial b = {>> {{<< {a}}}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingOperatorElaboration, RealTargetForStreamingSourceRejected) {
  // §11.4.14: a streaming_concatenation source requires a bit-stream-type
  // target; a real variable is not a bit-stream type and shall be rejected.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  real dst;\n"
      "  logic [7:0] a;\n"
      "  initial dst = {>> {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "target of a streaming concatenation source assignment must be a "
      "bit-stream type",
      4, "11.4.14"));
}

TEST(StreamingOperatorElaboration, EventTargetForStreamingSourceRejected) {
  // §11.4.14: event variables are likewise not bit-stream types.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  logic [7:0] a;\n"
      "  initial e = {>> {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "target of a streaming concatenation source assignment must be a "
      "bit-stream type",
      4, "11.4.14"));
}

TEST(StreamingOperatorElaboration, StreamingAsArithOperandRejected) {
  // §11.4.14: a streaming_concatenation appearing as a sub-operand of an
  // expression (here, the right operand of `+`) without a prior bit-stream
  // cast is illegal.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  initial dst = a + {>> {b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      4, "11.4.14"));
}

TEST(StreamingOperatorElaboration, StreamingAsAssignmentTarget) {
  // §11.4.14: a streaming_concatenation is a legal target of an assignment (the
  // unpack position). Elaboration shall accept it — the context walk marks the
  // left-hand side of an assignment as a valid streaming context.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  logic [15:0] src;\n"
      "  initial {>> {a, b}} = src;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingOperatorElaboration, ChandleTargetForStreamingSourceRejected) {
  // §11.4.14: the target of a streaming_concatenation source must be a
  // bit-stream data object (or another streaming_concatenation). A chandle is
  // not a bit-stream type, so it is rejected — a distinct non-bit-stream type
  // from the real/event cases above.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle c;\n"
      "  logic [7:0] a;\n"
      "  initial c = {>> {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "target of a streaming concatenation source assignment must be a "
      "bit-stream type",
      4, "11.4.14"));
}

// §11.4.14: a streaming concatenation re-orders the bits of its stream
// expressions without adding or dropping any, so it is as wide as those
// operands together -- eight bits for two four-bit literals. The slice size
// decides the order the bits leave in rather than how many there are, so it
// does not enter the sum.
TEST(StreamingOperatorElaboration,
     StreamingConcatWidthIsTheSumOfItsOperandWidths) {
  TypedefMap typedefs;
  Expr first;
  first.kind = ExprKind::kIntegerLiteral;
  first.text = "4'b1100";

  Expr second;
  second.kind = ExprKind::kIntegerLiteral;
  second.text = "4'b0011";

  Expr stream;
  stream.kind = ExprKind::kStreamingConcat;
  stream.op = TokenKind::kGtGt;
  stream.elements = {&first, &second};

  EXPECT_EQ(InferExprWidth(&stream, typedefs), 8u);
}

// §11.4.14 confines a streaming concatenation to an assignment or a bit-stream
// cast and names no statement it is allowed to stand in, so every position a
// statement holds a statement in is one the report reaches.
// ElaboratorOperationRules::WalkStmtsForStreamingContext in
// src/elaborator/elaborator_validate_operations_streaming.cpp had written out
// six of the thirteen child-statement links Stmt declares and now takes the
// list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. The seven cases below stand in
// the seven positions it was missing, each of which elaborated clean beforehand
// with the concatenation left in an operand position nothing objected to. Each
// writes the concatenation as the right operand of `+`, the form
// StreamingAsArithOperandRejected above establishes as illegal in an
// initial-block statement.

// A.6.3 gives `par_block ::= fork [ : block_identifier ]
// { block_item_declaration } { statement_or_null } join_keyword ...`, so a fork
// holds statements the way a begin-end block does. The parser keeps them in
// Stmt::fork_stmts rather than in Stmt::stmts.
TEST(StreamingOperatorElaboration,
     StreamingAsArithOperandInAForkStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  initial fork\n"
      "    dst = a + {>> {b}};\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      5, "11.4.14"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...`, so
// the loop header holds assignments of its own, kept in Stmt::for_inits.
TEST(StreamingOperatorElaboration,
     StreamingAsArithOperandInAForInitializerRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  int i;\n"
      "  initial\n"
      "    for (dst = a + {>> {b}}; i < 1; i = i + 1)\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      6, "11.4.14"));
}

// A.6.8's `for_step_assignment ::= operator_assignment | ...` is the same rule
// at the other end of the loop header, kept in Stmt::for_steps. The initializer
// here assigns a constant, so the report can only be about the step.
TEST(StreamingOperatorElaboration, StreamingAsArithOperandInAForStepRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; dst = a + {>> {b}})\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      6, "11.4.14"));
}

// A.6.10 gives `simple_immediate_assert_statement ::= assert ( expression )
// action_block` and §16.3 gives `action_block ::= statement_or_null |
// [ statement ] else statement_or_null`, so the pass arm of an immediate
// assertion holds an ordinary statement, kept in Stmt::assert_pass_stmt.
TEST(StreamingOperatorElaboration,
     StreamingAsArithOperandInAnAssertionPassStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  logic ok;\n"
      "  initial assert (ok) dst = a + {>> {b}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      5, "11.4.14"));
}

// The else arm of the same production, kept in Stmt::assert_fail_stmt, a link
// the pass-arm case above does not reach.
TEST(StreamingOperatorElaboration,
     StreamingAsArithOperandInAnAssertionFailStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  logic armed;\n"
      "  initial assert (armed) else dst = a + {>> {b}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      5, "11.4.14"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. §11.4.14
// judges where the concatenation is written rather than whether it runs, so the
// report stands whether the weighted draw would select the item or not.
TEST(StreamingOperatorElaboration,
     StreamingAsArithOperandInARandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  initial randcase 1: dst = a + {>> {b}}; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      4, "11.4.14"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(StreamingOperatorElaboration,
     StreamingAsArithOperandInARandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { dst = a + {>> {b}}; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "streaming concatenation shall not be used as an operand of an "
      "expression other than an assignment or bit-stream cast",
      6, "11.4.14"));
}

}  // namespace
