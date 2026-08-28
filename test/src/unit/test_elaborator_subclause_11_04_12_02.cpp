#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "helpers_eval_op.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StringConcatAndReplication, StringConcatElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string a, b, c;\n"
      "  initial begin\n"
      "    a = \"hello\";\n"
      "    b = \" world\";\n"
      "    c = {a, b};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringConcatAndReplication, StringReplicationElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial s = {3{\"ab\"}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringConcatAndReplication, NonConstantMultiplierAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    int n;\n"
      "    string s;\n"
      "    n = 3;\n"
      "    s = {n{\"boo \"}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringConcatAndReplication, StringConcatWithLiteralElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial s = {\"hello\", \" \", \"world\"};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringConcatAndReplication, StringConcatAppendElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = \"hello\";\n"
      "    s = {s, \" world\"};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringConcatAndReplication, StringConcatOnLhsBlockingAssignRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  initial {a, b} = \"hello\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            3, "11.4.12.2"));
}

TEST(StringConcatAndReplication, StringConcatOnLhsNonblockingAssignRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  initial {a, b} <= \"hello\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            3, "11.4.12.2"));
}

TEST(StringConcatAndReplication, StringConcatOnLhsContAssignRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  assign {a, b} = \"hello\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            3, "11.4.12.2"));
}

TEST(StringConcatAndReplication, BitConcatOnLhsStillAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  initial {a, b} = 8'hC3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.12.2 bars a concatenation of strings from the left-hand side of an
// assignment and names no statement the assignment is allowed to stand in, so
// every position a statement holds a statement in is one the report reaches.
// ElaboratorOperationRules::WalkStmtsForStringConcatLvalue in
// src/elaborator/elaborator_validate_operations_streaming.cpp had written out
// six of the thirteen child-statement links Stmt declares and now takes the
// list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. The seven cases below stand
// in the seven positions it was missing, each of which elaborated clean
// beforehand with the illegal left-hand side left unreported.

// A.6.3 gives `par_block ::= fork [ : block_identifier ]
// { block_item_declaration } { statement_or_null } join_keyword ...`, so a fork
// holds statements the way a begin-end block does. The parser keeps them in
// Stmt::fork_stmts rather than in Stmt::stmts.
TEST(StringConcatAndReplication, StringConcatOnLhsInAForkStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  initial fork\n"
      "    {a, b} = \"hello\";\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            4, "11.4.12.2"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// A.8.5 gives `variable_lvalue ::= ... | { variable_lvalue { , variable_lvalue
// } } | ...`, so a concatenation stands on the left of an assignment in a
// for-loop header. The parser keeps those assignments in Stmt::for_inits.
TEST(StringConcatAndReplication, StringConcatOnLhsInAForInitializerRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  int i;\n"
      "  initial\n"
      "    for ({a, b} = \"hello\"; i < 1; i = i + 1)\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            5, "11.4.12.2"));
}

// A.6.8's `for_step_assignment ::= operator_assignment | ...` is the same rule
// at the other end of the loop header, and A.6.2 gives `operator_assignment ::=
// variable_lvalue assignment_operator expression`. The parser keeps those in
// Stmt::for_steps. The initializer here assigns an integer, so the report can
// only be about the step.
TEST(StringConcatAndReplication, StringConcatOnLhsInAForStepRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; {a, b} = \"hello\")\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            5, "11.4.12.2"));
}

// A.6.10 gives `simple_immediate_assert_statement ::= assert ( expression )
// action_block` and §16.3 gives `action_block ::= statement_or_null |
// [ statement ] else statement_or_null`, so the pass arm of an immediate
// assertion holds an ordinary statement, kept in Stmt::assert_pass_stmt.
TEST(StringConcatAndReplication,
     StringConcatOnLhsInAnAssertionPassStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  logic ok;\n"
      "  initial assert (ok) {a, b} = \"hello\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            4, "11.4.12.2"));
}

// The else arm of the same production, kept in Stmt::assert_fail_stmt, a link
// the pass-arm case above does not reach.
TEST(StringConcatAndReplication,
     StringConcatOnLhsInAnAssertionFailStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  logic armed;\n"
      "  initial assert (armed) else {a, b} = \"hello\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            4, "11.4.12.2"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. §11.4.12.2
// judges the left-hand side rather than what runs, so the report stands whether
// the weighted draw would select the item or not.
TEST(StringConcatAndReplication, StringConcatOnLhsInARandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  initial randcase 1: {a, b} = \"hello\"; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            3, "11.4.12.2"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(StringConcatAndReplication,
     StringConcatOnLhsInARandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { {a, b} = \"hello\"; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string concatenation is not allowed on the "
                            "left-hand side of an assignment",
                            5, "11.4.12.2"));
}

}  // namespace
