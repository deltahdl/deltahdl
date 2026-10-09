#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SubroutineCallExprElaboration, MethodCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  function void method(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C obj = new;\n"
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
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module m;\n"
      "  C obj = new;\n"
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
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module m;\n"
      "  C obj = new;\n"
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

// A.8.2: a tf_call names a task or a function, so a bare call statement
// naming a variable (#5796), and a call with an argument list naming a
// variable or a net, as a statement or within an expression (#5798), are each
// reported where they are written.
TEST(SubroutineCallElaborationSyntax, ACallNamingAVariableOrANetIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  wire w;\n"
      "  int y;\n"
      "  initial begin\n"
      "    x;\n"
      "    y = x(1);\n"
      "    w();\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kMessage =
      "' names a variable or a net, and a call names a task or a function";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string("'x") + kMessage,
                            6, "A.8.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string("'x") + kMessage,
                            7, "A.8.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string("'w") + kMessage,
                            8, "A.8.2"));
}

// A.8.2: a call of a task or a function the module declares, a call through a
// class handle, a constructor call and a shallow copy of a handle (§8.12) name
// no variable as a call, so none is reported.
TEST(SubroutineCallElaborationSyntax, ACallOfATaskOrFunctionIsNotReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; function void g(); endfunction endclass\n"
      "module m;\n"
      "  task t; endtask\n"
      "  function int fn(); return 1; endfunction\n"
      "  C c, d;\n"
      "  int y;\n"
      "  initial begin\n"
      "    if (y == 0) t; else t();\n"
      "    c = new;\n"
      "    d = new c;\n"
      "    c.g();\n"
      "    y = fn();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// A.8.2 with §23.9: a call naming a variable a block or a fork declares is
// reported inside it, though the variable shadows a function of the module,
// and a call of that function outside the block is not (#5799).
TEST(SubroutineCallElaborationSyntax, ACallNamingABlocksVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int g(); return 1; endfunction\n"
      "  int y;\n"
      "  initial begin\n"
      "    begin int g; g; end\n"
      "    fork int z; z(); join\n"
      "    y = g();\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kMessage =
      "' names a variable or a net, and a call names a task or a function";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string("'g") + kMessage,
                            5, "A.8.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string("'z") + kMessage,
                            6, "A.8.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), std::string("'g") + kMessage,
                             7, "A.8.2"));
}

// A.6.9: a call statement calls a task or a function, so one naming a let, a
// sequence, a property, or a variable a package declares and the module
// imports by name or with a wildcard, is reported, while the let named with an
// argument list within an expression is not (#5800).
TEST(SubroutineCallElaborationSyntax,
     ACallStatementNamingNoSubroutineIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "package q; int u; endpackage\n"
      "package p; int v; int w; function void pf(); endfunction endpackage\n"
      "module m;\n"
      "  import p::v;\n"
      "  import q::*;\n"
      "  let l(a) = a;\n"
      "  sequence s; 1; endsequence\n"
      "  property pr; 1; endproperty\n"
      "  int y;\n"
      "  initial begin\n"
      "    l(1);\n"
      "    s;\n"
      "    pr;\n"
      "    v;\n"
      "    u;\n"
      "    y = l(2);\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kMessage =
      "' names no task or function, and a call statement calls one";
  for (const auto& [name, line] : {std::pair<const char*, uint32_t>{"l", 11},
                                   {"s", 12},
                                   {"pr", 13},
                                   {"v", 14},
                                   {"u", 15}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("'") + name + kMessage, line,
                              "A.6.9"))
        << name;
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), std::string("'l") + kMessage,
                             16, "A.6.9"));
}

}  // namespace
