#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §20.16: the output terms of a PLA modeling system task shall only be
// variables. A single variable output term elaborates cleanly.
TEST(PlaOutputTerms, VariableOutputIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  logic b;\n"
      "  initial $async$and$array(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16: a net used as the output term violates the shall and is rejected.
TEST(PlaOutputTerms, NetOutputIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  wire b;\n"
      "  initial $async$and$array(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "output terms of a PLA modeling system task shall be variables", 5,
      "20.16"));
}

// §20.16: a concatenation of variable output terms is permitted.
TEST(PlaOutputTerms, ConcatenatedVariableOutputIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a1, a2;\n"
      "  logic b1, b2, b3;\n"
      "  initial $sync$or$plane(mem, {a1, a2}, {b1, b2, b3});\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16: a concatenation of output terms that includes a net is rejected,
// because every output term must be a variable.
TEST(PlaOutputTerms, ConcatenatedOutputWithNetIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  logic b1;\n"
      "  wire b2;\n"
      "  initial $async$nor$array(mem, a, {b1, b2});\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "output terms of a PLA modeling system task shall be variables", 6,
      "20.16"));
}

// §20.16: the restriction applies only to output terms. An input term may be a
// net, so a net input paired with a variable output elaborates cleanly.
TEST(PlaOutputTerms, NetInputWithVariableOutputIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire a;\n"
      "  logic b;\n"
      "  initial $sync$nand$plane(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16, Table 20-12: the output-terms restriction applies only to the
// enumerated PLA tasks. A name whose logic component is not one of
// and/or/nand/nor is not a PLA task, so a net in its third argument does not
// trigger the rule. This pins the boundary of which names are recognized.
TEST(PlaOutputTerms, NonTableNameIsNotSubjectToTheRule) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  wire b;\n"
      "  initial $async$xor$array(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16, Table 20-12: a name carrying more than the three
// array_type/logic/format components is not one of the enumerated tasks, so the
// output-terms rule does not apply even with a net in the output position.
TEST(PlaOutputTerms, NameWithExtraComponentIsNotSubjectToTheRule) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  wire b;\n"
      "  initial $async$and$array$extra(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16: an output term may be a select of a variable, which remains a
// variable reference and is accepted.
TEST(PlaOutputTerms, BitSelectOfVariableOutputIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  logic [3:0] b;\n"
      "  initial $sync$or$array(mem, a, b[0]);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16: a select of a net still references a net, not a variable, so using it
// as an output term violates the shall and is rejected.
TEST(PlaOutputTerms, BitSelectOfNetOutputIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  wire [3:0] b;\n"
      "  initial $async$and$array(mem, a, b[0]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "output terms of a PLA modeling system task shall be variables", 5,
      "20.16"));
}

// §20.16, Syntax 20-16 (logic ::= and | or | nand | nor) and Table 20-12: the
// "or" logic component names a recognized PLA task. Because the output-terms
// rule fires only for a recognized task, rejecting a net output on a $..$or$..
// call discriminatingly witnesses that "or" is decoded as a valid logic form -
// an unrecognized name would leave the net output unflagged.
TEST(PlaOutputTerms, OrLogicTaskRecognizedSoNetOutputRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  wire b;\n"
      "  initial $async$or$array(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "output terms of a PLA modeling system task shall be variables", 5,
      "20.16"));
}

// §20.16, Syntax 20-16 (array_type ::= sync | async, logic ::= ... | nand,
// format ::= array | plane) and Table 20-12: a $sync$nand$plane call is a
// recognized task only if all three of its components decode as valid forms.
// Rejecting its net output discriminatingly witnesses recognition of the sync
// array type, the nand logic, and the plane format together - none of which is
// otherwise observed in a rejecting (recognition-dependent) context.
TEST(PlaOutputTerms, SyncNandPlaneTaskRecognizedSoNetOutputRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  wire b;\n"
      "  initial $sync$nand$plane(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "output terms of a PLA modeling system task shall be variables", 5,
      "20.16"));
}

// §20.16 states its rule over the arguments of a PLA modeling system task --
// "the input terms can be nets or variables whereas the output terms shall
// only be variables" -- and names no position the call may stand in. Each of
// the four cases below writes the call in one such position, and each is a
// position CheckPlaOutputTermsStmt in
// src/elaborator/elaborator_validate_queries.cpp reached only once it took its
// list of nested statements from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. Every one of them elaborated
// clean beforehand, with a net left driven as a PLA output term.
//
// Stmt::for_steps is the fifth position that list added and it carries no case
// here. A PLA task returns no value, so it is neither the right-hand side of
// the operator_assignment nor the inc_or_dec_expression A.6.8 admits as a
// for_step_assignment, and the third form A.6.8 admits, a
// function_subroutine_call, takes no terminating semicolon while the one form
// Syntax 20-16 defines ends in one.

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm.
// The parser keeps the pass arm in Stmt::assert_pass_stmt.
TEST(PlaOutputTerms, NetOutputInAnAssertionPassStatementIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] amem [1:3];\n"
      "  logic ain;\n"
      "  wire aout;\n"
      "  logic ready;\n"
      "  initial assert (ready) $sync$and$array(amem, ain, aout);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "output terms of a PLA modeling system task shall be variables", 6,
      "20.16"));
}

// §16.3's else arm of the same action block, kept in Stmt::assert_fail_stmt.
TEST(PlaOutputTerms, NetOutputInAnAssertionFailStatementIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] fmem [1:3];\n"
      "  logic fin;\n"
      "  wire fout;\n"
      "  logic done;\n"
      "  initial assert (done) else $async$nand$plane(fmem, fin, fout);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "output terms of a PLA modeling system task shall be variables", 6,
      "20.16"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. The rule
// is static, so it holds whether the weighted draw would select the item or
// not.
TEST(PlaOutputTerms, NetOutputInARandcaseItemIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] nmem [1:3];\n"
      "  logic nin;\n"
      "  wire nout;\n"
      "  initial randcase 1: $sync$nor$array(nmem, nin, nout); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "output terms of a PLA modeling system task shall be variables", 5,
      "20.16"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions.
TEST(PlaOutputTerms, NetOutputInARandsequenceCodeBlockIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] rmem [1:3];\n"
      "  logic rin;\n"
      "  wire rout;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { $async$or$plane(rmem, rin, rout); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "output terms of a PLA modeling system task shall be variables", 7,
      "20.16"));
}

}  // namespace
