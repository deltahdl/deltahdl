#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §6.20: "Constants are named data objects that never change. SystemVerilog
// provides three elaboration-time constants: parameter, localparam, and
// specparam." A procedural assignment that writes one breaks that sentence, and
// the sentence says nothing about the shape of the write or about where the
// statement making it stands. The cases in the numbered files beside this one
// cover the constants themselves; these cover the writes, one per shape the
// report used to be absent from.
//
// Every case here uses a parameter unless it says otherwise, because
// Elaborator::const_names_ takes the three kinds together and the report is the
// same for all three.

TEST(ConstAssignElaboration, ABitSelectWriteToAParameterIsReported) {
  // §11.5.1's bit-select selects one bit of a named object and stores into that
  // object, so the object written is the parameter and not the bit. This is the
  // shape with no lvalue validator behind it: the checks in
  // src/elaborator/elaborator_validate_operations_arrays.cpp judge whether a
  // select is well formed and never whether its target may be written.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter logic [7:0] P = 8'hFF;\n"
      "  initial P[3] = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, APartSelectWriteToAParameterIsReported) {
  // The same shape with a range rather than a single index. It is a case of its
  // own because a repair that unwrapped one particular select form would reach
  // one and not the other.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter logic [7:0] P = 8'hFF;\n"
      "  initial P[7:4] = 4'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, AConcatenationWriteToAParameterIsReported) {
  // §11.4.12 makes a concatenation a legal left-hand side, and each operand of
  // one is written. The parameter is the second operand, so a walk that asked
  // only about the first would pass this source.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial {i, P} = 8'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterFromATaskBodyIsReported) {
  // §9.2 counts a task a structured procedure. Its statements are not under
  // ModuleItem::body, so no unwrapping of the left-hand side reaches this
  // source: the body has to be walked for the write to be seen at all.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  task t;\n"
      "    P = 7;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterFromAFunctionBodyIsReported) {
  // The same for a function, which ModuleItemKind gives a kind of its own, so a
  // repair naming the task kind alone would miss it.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  function int fn;\n"
      "    P = 7;\n"
      "    return P;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInsideForkIsReported) {
  // §9.3.2's fork-join keeps its statements in a member of its own, which the
  // walk did not visit.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  initial fork\n"
      "    P = 1;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInAForInitializerIsReported) {
  // §12.7.1's for loop holds its initialization statements apart from its body,
  // and a write there is a write.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial for (P = 0; i < 2; i = i + 1) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInAForStepIsReported) {
  // The step assignments are a third member again, so this is a case of its own
  // rather than the initializer case restated.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 2; P = P + 1) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, ABitSelectWriteToALocalparamIsReported) {
  // §6.20 names localparam beside parameter, so a repair that narrowed to the
  // parameter keyword would leave this source accepted.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  localparam logic [7:0] L = 8'hFF;\n"
      "  initial L[0] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'L'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, AnElementWriteToAStringParameterIsReported) {
  // §6.16's string is indexed like any other named object, so a write to one of
  // its bytes writes the parameter. The report has to be made here: at run time
  // a parameter is an ordinary variable, and the write reaches the string path
  // in src/simulator/statement_assign_core.cpp with nothing left to refuse it.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter string S = \"abc\";\n"
      "  initial S[0] = \"X\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'S'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAVariableThroughABitSelectIsAccepted) {
  // The other side of the first case: the same shape over a name that is not a
  // constant is a write the standard allows, so widening the check must not
  // have made every select of a name a report.
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  logic [7:0] v;\n"
             "  initial v[3] = 1'b0;\n"
             "endmodule\n"));
}

// §6.16.2's putc "replaces the ith character in str with the given integral
// value", so the call writes S, and §6.20 says a constant never changes. A call
// is not an assignment, so no walk over left-hand sides reaches it: at run time
// a parameter is an ordinary variable with no flag marking it constant, and the
// write reached StringWriteByte with nothing left to refuse it.
TEST(ConstAssignElaboration, APutcOnAStringParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter string S = \"abc\";\n"
      "  initial S.putc(0, \"X\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'S'",
                            3, "6.20"));
}

// §6.16.10's itoa "stores the ASCII decimal representation of i into str". It
// reaches a different helper from putc, so a repair naming one method would
// leave the other five.
TEST(ConstAssignElaboration, AnItoaOnAStringParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter string S = \"abc\";\n"
      "  initial S.itoa(7);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'S'",
                            3, "6.20"));
}

// The last of the six, over the second of §6.20's three constant kinds, so the
// pair that is not the first of each is covered too.
TEST(ConstAssignElaboration, ARealtoaOnAStringLocalparamIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  localparam string S = \"abc\";\n"
      "  initial S.realtoa(1.5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'S'",
                            3, "6.20"));
}

// The same call over an ordinary string variable, which is what the method is
// for. Without this a repair could report every mutating call and pass the
// three cases above.
TEST(ConstAssignElaboration, APutcOnAStringVariableIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  string s = \"abc\";\n"
             "  initial s.putc(0, \"X\");\n"
             "endmodule\n"));
}

// §6.16.3's getc "returns the ASCII code of the ith character in str" and
// writes nothing, so it stays legal on a constant. This is what keeps the check
// on whether the method writes its object rather than on whether a string
// method was called on a constant at all.
TEST(ConstAssignElaboration, AGetcOnAStringParameterIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  parameter string S = \"abc\";\n"
             "  byte b;\n"
             "  initial b = S.getc(0);\n"
             "endmodule\n"));
}

// §6.20 says a constant never changes and puts no condition on where the write
// that would change one stands, so every position a statement holds a statement
// in is a position the report is made at. The cases below cover one such
// position each, and between them they cover every child-statement link Stmt
// declares that no case above already reaches.
// Elaborator::WalkStmtsForConstAssign takes that list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h instead of writing its own, so
// a link dropped from the shared list drops §6.20 from that position with it,
// and these are the cases that go red when it does.

// A.6.3 gives `seq_block ::= begin [ : block_identifier ] {
// block_item_declaration } { statement_or_null } end`, whose statements the
// parser keeps in Stmt::stmts.
TEST(ConstAssignElaboration, AWriteToAParameterInABeginEndBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  initial begin\n"
      "    P = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

// §12.4's conditional statement holds a statement per branch, kept in
// Stmt::then_branch and Stmt::else_branch. This case and the next cover one
// branch each, because a walk reaches one member without the other.
TEST(ConstAssignElaboration, AWriteToAParameterInAnIfBranchIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial if (i == 0) P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

// The else arm of the same statement. Its then arm writes i, so the report the
// case reads can only have come from the else arm.
TEST(ConstAssignElaboration, AWriteToAParameterInAnElseBranchIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial if (i == 0) i = 1; else P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

// §12.7.4's while loop holds its statement in Stmt::body, which the parser also
// fills for forever, repeat, foreach and do-while, so one case answers for the
// member. §6.20 is broken by the write being written, whether the loop would
// run it or not.
TEST(ConstAssignElaboration, AWriteToAParameterInAWhileBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial while (i < 2) P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

// §12.7.1's for loop holds its body in Stmt::for_body, a fourth member beside
// the initializers and the steps the two cases above cover. The initializer and
// the step here write i, so the report the case reads is the body's.
TEST(ConstAssignElaboration, AWriteToAParameterInAForBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 2; i = i + 1) P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

// §12.5's case statement holds a statement per item, kept in
// Stmt::case_items rather than in Stmt::stmts.
TEST(ConstAssignElaboration, AWriteToAParameterInACaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial\n"
      "    case (i)\n"
      "      0: P = 1;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            6, "6.20"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, kept in
// Stmt::randcase_items. §6.20 is a rule about the source, so it holds whether
// the weighted draw would select the item or not.
TEST(ConstAssignElaboration, AWriteToAParameterInARandcaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  initial randcase 1: P = 1; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            3, "6.20"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(ConstAssignElaboration,
     AWriteToAParameterInAnAssertionPassStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  logic ok;\n"
      "  initial assert (ok) P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration,
     AWriteToAParameterInAnAssertionFailStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  logic ok;\n"
      "  initial assert (ok) else P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(ConstAssignElaboration,
     AWriteToAParameterInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { P = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            5, "6.20"));
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it.
TEST(ConstAssignElaboration,
     AWriteToAParameterInARandsequenceWeightCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := 1 { P = 1; };\n"
      "      a : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            6, "6.20"));
}

}  // namespace
