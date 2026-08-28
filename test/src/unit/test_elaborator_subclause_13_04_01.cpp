#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(FunctionReturnElaboration, FunctionDeclInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function int add(input int a, input int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FunctionReturnElaboration, VoidFunctionReturnWithValueError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function returns a value", 3, "13.4.1"));
}

// §13.4.1: the report that rejects a return statement carrying a value in a
// void function names the subclause stating the rule, so a caller learns which
// rule was enforced without matching the wording of the message.
TEST(FunctionReturnElaboration,
     ReturnStatementWithAValueInAVoidFunctionNames13_4_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function returns a value", 3, "13.4.1"));
}

TEST(FunctionReturnElaboration, FunctionCallAsExprElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] add_one(input logic [7:0] v);\n"
      "    return v + 8'd1;\n"
      "  endfunction\n"
      "  initial x = add_one(8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionReturnElaboration, NestedCallsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(int n); return n + 1; endfunction\n"
      "  function int g(int n); return n * 2; endfunction\n"
      "  logic [31:0] x;\n"
      "  initial x = f(g(3));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionReturnElaboration, VarSameNameAsFunctionInsideBody) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int foo();\n"
      "    int foo;\n"
      "    foo = 1;\n"
      "    return foo;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of 'foo' conflicts with function name",
                            3, "13.4.1"));
}

TEST(FunctionReturnElaboration, FunctionNameAssignElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int compute(input int a);\n"
      "    compute = a * 2;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionReturnElaboration, VoidFunctionElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function void log(int v);\n"
             "    $display(\"%0d\", v);\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(FunctionReturnElaboration, VoidFunctionBareReturnOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function void f();\n"
             "    $display(\"hello\");\n"
             "    return;\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(FunctionReturnElaboration, NonVoidFunctionBareReturnError) {
  // §13.4: when the return statement is used, nonvoid functions shall specify
  // an expression with the return; a bare `return;` here is an error. The
  // report comes from CheckValueReturningFuncReturn, which cites §12.8 rather
  // than §13.4.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f();\n"
      "    return;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return statement in non-void function 'f' shall "
                            "have an expression",
                            3, "12.8"));
}

TEST(FunctionReturnElaboration, VoidReturnWithValueInNestedBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    if (1) begin\n"
      "      return 42;\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function returns a value", 4, "13.4.1"));
}

TEST(FunctionReturnElaboration, VoidFunctionAsOperandError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void nop(); endfunction\n"
      "  logic [31:0] x;\n"
      "  initial x = nop();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function 'nop' used as expression operand", 4,
                            "13.4.1"));
}

TEST(FunctionReturnElaboration, VoidFunctionAsStatementOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void nop(); endfunction\n"
      "  initial begin\n"
      "    nop();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionReturnElaboration, VoidFunctionInContAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void nop(); endfunction\n"
      "  wire w;\n"
      "  assign w = nop();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function 'nop' used as expression operand", 4,
                            "13.4.1"));
}

TEST(FunctionReturnElaboration, VoidFunctionAsArgError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void nop(); endfunction\n"
      "  function int f(int x); return x; endfunction\n"
      "  logic [31:0] x;\n"
      "  initial x = f(nop());\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function 'nop' used as expression operand", 5,
                            "13.4.1"));
}

TEST(FunctionReturnElaboration, NonvoidCallAsStatementWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int compute(); return 7; endfunction\n"
      "  initial begin\n"
      "    compute();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(FunctionReturnElaboration, VoidCastSuppressesDiscardWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int compute(); return 7; endfunction\n"
      "  initial begin\n"
      "    void'(compute());\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(FunctionReturnElaboration, VoidCallAsStatementDoesNotWarn) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void nop(); endfunction\n"
      "  initial begin\n"
      "    nop();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(FunctionReturnElaboration, NonvoidCallAsRhsDoesNotWarn) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int compute(); return 7; endfunction\n"
      "  logic [31:0] x;\n"
      "  initial x = compute();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(FunctionReturnElaboration,
     ObjectWithFunctionNameInDeclaringScopeIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int dup(); return 0; endfunction\n"
      "  logic [7:0] dup;\n"
      "endmodule\n",
      f);
  // The rule that fires is the §23.9 same-scope redeclaration one, reported
  // against the variable because the function registered the name first.
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'dup'", 3, "23.9"));
}

TEST(FunctionReturnElaboration, NonvoidCallMissingParensIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f(); return 1; endfunction\n"
      "  initial begin\n"
      "    f;\n"
      "  end\n"
      "endmodule\n",
      f);
  // §13.5.5 owns the omitted-parentheses rule; §13.4.1 has no report for it.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot omit parentheses in call to nonvoid "
                            "function 'f'",
                            4, "13.5.5"));
}

TEST(FunctionReturnElaboration, SystemFunctionAllowedAsImplicitVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial x = $random;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The four cases below cover the positions CheckFuncBodyStmt in
// src/elaborator/elaborator_validate_funcbody.cpp reaches for the first time
// now that it takes its child-statement links from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. It had written out nine of the
// thirteen links Stmt declares, so §13.4.1's two reports -- and §13.4's and
// §10.6.1's beside them -- went unmade for a statement written in
// Stmt::fork_stmts, Stmt::for_inits, Stmt::for_steps or Stmt::rs_productions.
//
// Stmt::for_inits gets no case: A.6.8 admits only a
// list_of_variable_assignments or a for_variable_declaration there, and neither
// is a return or a declaration the elaborator sees as a StmtKind::kVarDecl.
// Stmt::for_steps does hold a function_subroutine_call, and
// FunctionElaboration.TaskEnabledFromAForStepError in
// test/src/unit/test_elaborator_subclause_13_04.cpp covers it, the rule that
// reaches a for step being §13.4's rather than §13.4.1's.

// §9.3.2 already rejected this return, through CheckNoReturnInFork, but
// §13.4.1's own report about the value it carries was never made: nothing in
// CheckFuncBodyStmt descended into a fork. §13.4.4 exempts the statements under
// a fork-join_none -- "Within a function, a fork-join_none construct may
// contain any statements that are legal within a task" -- and the walk still
// stops at one, so the fork here is the fork-join §13.4 rule a) forbids
// outright.
TEST(FunctionReturnElaboration, VoidFunctionReturnWithValueInsideAForkJoin) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    fork\n"
      "      return 1;\n"
      "    join\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function returns a value", 4, "13.4.1"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds the data declaration
// §13.4.1's "It shall also be illegal to declare another object with the same
// name as the function inside the function scope" is about. The parser keeps it
// in RsProd::code_stmts, reached through Stmt::rs_productions and through no
// other member of Stmt.
TEST(FunctionReturnElaboration, VarNamedAsFunctionInARandsequenceCodeBlock) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    randsequence(main)\n"
      "      main : { int f; };\n"
      "    endsequence\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of 'f' conflicts with function name",
                            4, "13.4.1"));
}

// A.6.12's `rs_rule ::= rs_production_list [ := weight_specification [
// rs_code_block ] ]` puts a second code block after the weight, kept in
// RsRule::weight_code rather than in RsProd::code_stmts, so it is a second
// statement position under Stmt::rs_productions and gets its own case.
TEST(FunctionReturnElaboration,
     VarNamedAsFunctionInARandsequenceWeightCodeBlock) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    randsequence(main)\n"
      "      main : alt := 5 { int f; };\n"
      "      alt : { ; };\n"
      "    endsequence\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of 'f' conflicts with function name",
                            4, "13.4.1"));
}

// The §18.17.6 case: what a return written in a randsequence production code
// block is, and what §13.4.1 therefore owes it. "The return statement aborts
// the generation of the current production", and §18.17.7 adds that "A value is
// returned from a production by using the return with an expression", so a
// production declared `int` returns its value exactly the way §13.4.1's "void
// function returns a value" report fires -- a return carrying an expression.
// Neither return below is the function's, so neither is that report's. Take
// FunctionBodyScope::in_production_code_block in
// src/elaborator/elaborator_validate_funcbody.cpp away and §18.17.7's own
// construct is rejected inside a void function.
TEST(FunctionReturnElaboration, ValueReturningProductionInAVoidFunctionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    randsequence(main)\n"
      "      void main : a { return; };\n"
      "      int a : { return 7; };\n"
      "    endsequence\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
