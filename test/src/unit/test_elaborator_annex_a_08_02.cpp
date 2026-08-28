#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SubroutineCallExprElaboration, MethodCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin obj.method(); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, SystemCallStatementElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial $display(\"hello\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, TfCallNoArgsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t; endtask\n"
      "  initial t();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, TfCallWithPositionalArgsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(int a, int b); return a + b; endfunction\n"
      "  int x;\n"
      "  initial x = f(1, 2);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, ConstantFunctionCallInParameterElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(int a); return a + 1; endfunction\n"
      "  parameter P = f(3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, SystemTfCallBareElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, NamedArgumentsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(int a, int b); return a - b; endfunction\n"
      "  int x;\n"
      "  initial x = f(.a(10), .b(3));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, MixedPositionalAndNamedArgsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(int a, int b, int c); return a + b + c; endfunction\n"
      "  int x;\n"
      "  initial x = f(1, 2, .c(3));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, RandomizeBasicElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin obj.randomize(); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, TaskCallWithoutParensElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t; endtask\n"
      "  initial t;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, VoidFunctionCallWithoutParensElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void log; endfunction\n"
      "  initial log;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, NonVoidFunctionCallWithoutParensRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f; return 1; endfunction\n"
      "  initial f;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot omit parentheses in call to nonvoid function 'f'", 3, "13.5.5"));
}

TEST(SubroutineCallExprElaboration, ScopeRandomizeWithNullRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin randomize(null); end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 2, "A.8.2"));
}

TEST(SubroutineCallExprElaboration, StdRandomizeWithNullRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin std::randomize(null); end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 2, "A.8.2"));
}

TEST(SubroutineCallExprElaboration, ScopeRandomizeWithParenIdListRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin randomize() with (a) { a > 0; }; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "scope randomize call cannot use a parenthesized "
                            "identifier list after 'with'",
                            2, "A.8.2"));
}

TEST(SubroutineCallExprElaboration,
     ClassMethodRandomizeWithParenIdListAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin obj.randomize() with (a) { a > 0; }; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// constant_function_call folded in a constant-expression context where the
// call's argument is itself a parameter (a distinct constant form from the
// literal used in ConstantFunctionCallInParameterElaborates). The elaborator
// must resolve the parameter before folding the call.
TEST(SubroutineCallExprElaboration, ConstantFunctionCallWithParameterArg) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int B = 41;\n"
      "  function int inc(int n); return n + 1; endfunction\n"
      "  localparam int P = inc(B);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// constant_function_call folded where the argument is a localparam constant.
TEST(SubroutineCallExprElaboration, ConstantFunctionCallWithLocalparamArg) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int B = 41;\n"
      "  function int inc(int n); return n + 1; endfunction\n"
      "  localparam int P = inc(B);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Footnote 43 of A.8.2 bars `null` from the argument list of a scope
// randomize_call and puts no condition on where that call is written; A.6.4
// makes a subroutine_call_statement a statement_item, so every position a
// statement holds a statement in is a position the report is owed at.
// WalkStmtForScopeRandomize in
// src/elaborator/elaborator_validate_subroutine_args.cpp had written out eight
// of the thirteen child-statement links Stmt declares, and now takes the list
// from ForEachChildStmt in src/elaborator/elaborator_validate_internal.h. The
// cases below cover one newly reached position each.

// A.6.3's par_block holds statement_or_null between fork and its join_keyword,
// which the parser keeps in Stmt::fork_stmts.
TEST(SubroutineCallExprElaboration, ScopeRandomizeWithNullInForkArmRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial fork\n"
      "    randomize(null);\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 3, "A.8.2"));
}

// A.6.3's action_block gives an immediate assertion a statement in each arm,
// held in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(SubroutineCallExprElaboration,
     ScopeRandomizeWithNullInAssertionPassStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial assert (1) randomize(null);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 2, "A.8.2"));
}

TEST(SubroutineCallExprElaboration,
     ScopeRandomizeWithNullInAssertionFailStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial assert (1) else randomize(null);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 2, "A.8.2"));
}

// §18.16's `randcase_item ::= expression : statement_or_null` puts a statement
// after each weight, held in Stmt::randcase_items.
TEST(SubroutineCallExprElaboration,
     ScopeRandomizeWithNullInRandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial randcase\n"
      "    1 : randomize(null);\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 3, "A.8.2"));
}

// A.6.12's rs_code_block holds procedural statements, which the parser keeps in
// RsProd::code_stmts under Stmt::rs_productions.
TEST(SubroutineCallExprElaboration,
     ScopeRandomizeWithNullInRandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { randomize(null); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 4, "A.8.2"));
}

// §18.17.1 admits a code block after a rule's weight specification, kept in
// RsRule::weight_code. That is a second statement list under
// Stmt::rs_productions, reached by a different member from the case above.
TEST(SubroutineCallExprElaboration,
     ScopeRandomizeWithNullInRandsequenceWeightCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { randomize(null); };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 5, "A.8.2"));
}

}  // namespace
