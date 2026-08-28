

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(UnpackedArrayConcatElaboration, EmptyConcatElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = {};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, ScalarItemsElaborate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[3];\n"
      "  initial A = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(UnpackedArrayConcatElaboration, ArrayItemExpansion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A [0:1] = '{10, 20};\n"
      "  int B [0:1] = '{30, 40};\n"
      "  int C [0:3];\n"
      "  initial begin\n"
      "    C = {A, B};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* c0 = f.ctx.FindVariable("C[0]");
  auto* c1 = f.ctx.FindVariable("C[1]");
  auto* c2 = f.ctx.FindVariable("C[2]");
  auto* c3 = f.ctx.FindVariable("C[3]");
  ASSERT_NE(c0, nullptr);
  ASSERT_NE(c1, nullptr);
  ASSERT_NE(c2, nullptr);
  ASSERT_NE(c3, nullptr);
  EXPECT_EQ(c0->value.ToUint64(), 10u);
  EXPECT_EQ(c1->value.ToUint64(), 20u);
  EXPECT_EQ(c2->value.ToUint64(), 30u);
  EXPECT_EQ(c3->value.ToUint64(), 40u);
}

// §10.10: a `{...}` concatenation initializing an unpacked/dynamic/queue array
// *declaration* is an unpacked array concatenation, where unsized integer
// literals are legal (unlike a packed §11.4.12 concatenation). The declaration-
// initializer path is distinct from the procedural-assignment path above, and
// previously applied the packed unsized-constant check, rejecting these.
TEST(UnpackedArrayConcatElaboration, DynamicArrayDeclInitUnsizedLiterals) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b[] = { 1, 2, 3, 4 };\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, QueueDeclInitUnsizedLiterals) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$] = { 10, 20, 30 };\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, FixedArrayDeclInitUnsizedLiterals) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a[3] = { 4, 5, 6 };\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Negative guard: a `{...}` initializing a plain packed vector (not an array)
// is a genuine §11.4.12 packed concatenation, where unsized constants remain
// illegal. The declaration-initializer exception must not swallow this.
TEST(UnpackedArrayConcatElaboration, PackedVectorDeclInitUnsizedStillErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x = { 1, 2 };\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unsized constant is not allowed in a concatenation", 2, "11.4.12"));
}

TEST(UnpackedArrayConcatElaboration, AssociativeArrayTargetError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  initial aa = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation cannot target an "
                            "associative array",
                            3, "10.10"));
}

TEST(UnpackedArrayConcatElaboration, QueueTargetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, DynamicArrayTargetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int d[];\n"
      "  initial d = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// "An unpacked array concatenation may appear as the source expression in an
// assignment-like context and shall not appear in any other context." A
// fixed-size unpacked target is one of the three legal slowest-varying
// dimensions (fixed-size, queue, dynamic). Mixing array and scalar items in
// the source — the LRM's `{A, 4, 5, A, 6}` shape — must elaborate cleanly.
TEST(UnpackedArrayConcatElaboration, MixedItemsForFixedSizeTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[1:3] = '{1, 2, 3};\n"
      "  int B[1:9];\n"
      "  initial B = {A, 4, 5, A, 6};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Items in an unpacked array concatenation must have a self-determined type.
// A bare brace expression nested inside the outer concatenation has no
// self-determined type when its width does not match the target element
// width (and so cannot represent a single element), so the elaborator shall
// reject the assignment.
TEST(UnpackedArrayConcatElaboration, NestedBraceItemRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A3[1:3];\n"
      "  int A9[1:9];\n"
      "  initial A9 = {A3, {32'd4, 32'd5, 32'd6, 32'd7, 32'd8, 32'd9}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  // The report is the §10.10.3 nesting prohibition, which is where the
  // self-determined-type requirement this case is about is written down.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nested concatenation in unpacked array "
                            "concatenation is not self-determined",
                            4, "10.10.3"));
}

// The literal `null` is only a legal item when the target's element type is
// event, class, interface class, chandle, or virtual interface. An int array
// target does not qualify, so a null item is rejected.
TEST(UnpackedArrayConcatElaboration, NullItemRejectedForIntElementType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {1, null, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array "
                            "concatenation for this target element type",
                            3, "10.10"));
}

// A chandle array's element type is explicitly listed by the rule as allowing
// null items, so an unpacked concatenation containing null shall elaborate
// without errors.
TEST(UnpackedArrayConcatElaboration, NullItemAllowedForChandleElementType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle q[$];\n"
      "  initial q = {null, null};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The rule also lists class (and interface class) as element types for which a
// null item is legal — a distinct acceptance branch from chandle, since a class
// handle reaches the check as a named element type rather than a built-in
// chandle. A queue of class handles initialized from a concatenation of null
// items shall therefore elaborate cleanly.
TEST(UnpackedArrayConcatElaboration, NullItemAllowedForClassElementType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C q[$];\n"
      "  initial q = {null, null};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// `event` is the third element type the rule admits for a null item, and it
// reaches the check through yet another branch (a built-in event element type,
// neither chandle nor a named class). A queue of events initialized from a
// concatenation of null items shall elaborate without errors, completing the
// per-element-type coverage of the accept side of the rule.
TEST(UnpackedArrayConcatElaboration, NullItemAllowedForEventElementType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event q[$];\n"
      "  initial q = {null, null};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.10 admits `null` as an item of an unpacked array concatenation only where
// the target's element type has a null value, and says nothing about the
// statement the assignment is written in.
//
// ElaboratorOperationRules::WalkStmtsForArrayConcatNesting in
// src/elaborator/elaborator_validate_operations_arrays.cpp reached six of the
// thirteen statement links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states. The seven cases here
// each put `q = {1, null, 3}` on a queue of ints in one of the seven positions
// it did not read, where the item reached CheckNullItemInArrayConcatAssign not
// at all.
//
// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword [ :
// block_identifier ]`, so a fork arm is a statement position like any other.
TEST(UnpackedArrayConcatElaboration,
     NullItemInArrayConcatInAForkArmNames10_10) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    fork\n"
      "      q = {1, null, 3};\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array", 5,
                            "10.10"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case covers
// the pass arm and the one below it the fail arm.
TEST(UnpackedArrayConcatElaboration,
     NullItemInArrayConcatInAnAssertionPassStatementNames10_10) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  logic ok;\n"
      "  initial assert (ok) q = {1, null, 3};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array", 4,
                            "10.10"));
}

TEST(UnpackedArrayConcatElaboration,
     NullItemInArrayConcatInAnAssertionFailStatementNames10_10) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  logic ok;\n"
      "  initial assert (ok) else q = {1, null, 3};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array", 4,
                            "10.10"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. The rule
// is a static one, so it holds whether the weighted draw would select the item
// or not.
TEST(UnpackedArrayConcatElaboration,
     NullItemInArrayConcatInARandcaseItemNames10_10) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial randcase 1: q = {1, null, 3}; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array", 3,
                            "10.10"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions.
TEST(UnpackedArrayConcatElaboration,
     NullItemInArrayConcatInARandsequenceCodeBlockNames10_10) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { q = {1, null, 3}; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array", 5,
                            "10.10"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments |
// for_variable_declaration { , for_variable_declaration }` and
// `for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call`. A.6.2 gives `variable_assignment ::=
// variable_lvalue = expression` and `operator_assignment ::= variable_lvalue
// assignment_operator expression`, whose assignment_operator includes `=`, so
// an assignment stands at each of the two positions: this case writes one at
// the initialization and the case below it writes one at the step.
TEST(UnpackedArrayConcatElaboration,
     NullItemInArrayConcatInAForLoopInitializationNames10_10) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  int i;\n"
      "  initial for (q = {1, null, 3}; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array", 4,
                            "10.10"));
}

TEST(UnpackedArrayConcatElaboration,
     NullItemInArrayConcatInAForLoopStepNames10_10) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; q = {1, null, 3}) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array", 4,
                            "10.10"));
}

// §10.10 requires the target of an unpacked array concatenation to be an array
// whose slowest-varying dimension is unpacked fixed-size, queue or dynamic, and
// says "A target of any other type (including associative array) shall be
// illegal". It names no statement the assignment is allowed to stand in
// unjudged. WalkStmtsForAssocConcatTarget in
// src/elaborator/elaborator_validate_cast_ops.cpp had written out six of the
// thirteen child-statement links Stmt declares and now takes the list from
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h. The seven
// cases below are UnpackedArrayConcatElaboration.AssociativeArrayTargetError
// above rewritten in the seven positions the walk was missing, each of which
// elaborated clean beforehand with the associative-array target unreported.

// A.6.3 gives `par_block ::= fork [ : block_identifier ]
// { block_item_declaration } { statement_or_null } join_keyword ...`, so a fork
// holds statements the way a begin-end block does. The parser keeps them in
// Stmt::fork_stmts rather than in Stmt::stmts.
TEST(UnpackedArrayConcatElaboration, AssociativeArrayTargetInForkArmError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  initial fork\n"
      "    aa = {1, 2, 3};\n"
      "  join\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation cannot target an "
                            "associative array",
                            4, "10.10"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// A.6.2 gives `variable_assignment ::= variable_lvalue = expression`, so the
// assignment §10.10 judges stands in a for-loop header. The parser keeps those
// assignments in Stmt::for_inits.
TEST(UnpackedArrayConcatElaboration,
     AssociativeArrayTargetInForInitializerError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int i;\n"
      "  initial\n"
      "    for (aa = {1, 2, 3}; i < 1; i = i + 1)\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation cannot target an "
                            "associative array",
                            5, "10.10"));
}

// A.6.8's `for_step_assignment ::= operator_assignment | ...` is the same rule
// at the other end of the loop header, kept in Stmt::for_steps. The
// initializer here assigns an integer, so the report can only be about the
// step.
TEST(UnpackedArrayConcatElaboration, AssociativeArrayTargetInForStepError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; aa = {1, 2, 3})\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation cannot target an "
                            "associative array",
                            5, "10.10"));
}

// A.6.10 gives `simple_immediate_assert_statement ::= assert ( expression )
// action_block` and §16.3 gives `action_block ::= statement_or_null |
// [ statement ] else statement_or_null`, so the pass arm of an immediate
// assertion holds an ordinary statement, kept in Stmt::assert_pass_stmt.
TEST(UnpackedArrayConcatElaboration,
     AssociativeArrayTargetInAssertionPassStatementError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  logic ok;\n"
      "  initial assert (ok) aa = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation cannot target an "
                            "associative array",
                            4, "10.10"));
}

// The else arm of the same production, kept in Stmt::assert_fail_stmt, a link
// the pass-arm case above does not reach.
TEST(UnpackedArrayConcatElaboration,
     AssociativeArrayTargetInAssertionFailStatementError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  logic armed;\n"
      "  initial assert (armed) else aa = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation cannot target an "
                            "associative array",
                            4, "10.10"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. §10.10
// judges the assignment as written rather than what runs, so the report stands
// whether the weighted draw would select the item or not.
TEST(UnpackedArrayConcatElaboration,
     AssociativeArrayTargetInRandcaseItemError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  initial randcase 1: aa = {1, 2, 3}; endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation cannot target an "
                            "associative array",
                            3, "10.10"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(UnpackedArrayConcatElaboration,
     AssociativeArrayTargetInRandsequenceCodeBlockError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { aa = {1, 2, 3}; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation cannot target an "
                            "associative array",
                            5, "10.10"));
}

}  // namespace
