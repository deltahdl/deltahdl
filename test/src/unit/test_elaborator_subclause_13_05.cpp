#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SubroutineCallElaboration, FunctionCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int foo(int a); return a + 1; endfunction\n"
      "  int x;\n"
      "  initial x = foo(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaboration, OutputArgLiteralError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  initial foo(42);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'x' requires a variable", 5,
                            "13.5"));
}

TEST(SubroutineCallElaboration, InoutArgLiteralError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void foo(inout int x);\n"
      "    x = x + 1;\n"
      "  endfunction\n"
      "  initial foo(42);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "inout argument 'x' requires a variable", 5,
                            "13.5"));
}

TEST(SubroutineCallElaboration, OutputArgVariableOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int y;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  initial foo(y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaboration, TooManyArgsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int foo(int a); return a; endfunction\n"
      "  int x;\n"
      "  initial x = foo(1, 2, 3);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "too many arguments to 'foo': expected 1, got 3", 4,
                            "13.5"));
}

TEST(SubroutineCallElaboration, TooFewArgsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int foo(int a, int b); return a + b; endfunction\n"
      "  int x;\n"
      "  initial x = foo(1);\n"
      "endmodule\n",
      f);
  // The omitted argument has no default, so the rule that fires is §13.5.3
  // rather than §13.5.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "missing argument 'b' in call to 'foo'", 4,
                            "13.5.3"));
}

TEST(SubroutineCallElaboration, InoutArgVariableOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int y;\n"
      "  function void foo(inout int x);\n"
      "    x = x + 1;\n"
      "  endfunction\n"
      "  initial foo(y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, VoidCastElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int foo(); return 1; endfunction\n"
      "  initial void'(foo());\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, TaskCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task set_x;\n"
      "    x = 8'd1;\n"
      "  endtask\n"
      "  initial set_x();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, VoidCastOfMethodCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial void'(obj.method());\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, FunctionCallReturnValueElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] get_val(); return 8'd42; endfunction\n"
      "  initial x = get_val();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaboration, OutputArgSelectOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:3];\n"
      "  function void get(output logic [7:0] v);\n"
      "    v = 8'd1;\n"
      "  endfunction\n"
      "  initial get(arr[0]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaboration, VoidFunctionAsOperandError) {
  // Only a nonvoid function call may appear as an operand within an
  // expression; using a void function call as an operand is illegal.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function void set_x;\n"
      "    x = 8'd1;\n"
      "  endfunction\n"
      "  initial x = set_x() + 8'd1;\n"
      "endmodule\n",
      f);
  // The report that rejects the operand names §13.4.1 rather than §13.5.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function 'set_x' used as expression operand",
                            6, "13.4.1"));
}

TEST(SubroutineCallElaboration, OutputArgConcatenationOk) {
  // §13.5: an output actual may be any expression valid as a procedural-
  // assignment lvalue (§10.4). A concatenation of variables is such an lvalue,
  // so binding it to an output formal must elaborate without error.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  function void get(output logic [7:0] o);\n"
      "    o = 8'hAB;\n"
      "  endfunction\n"
      "  initial get({a, b});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaboration, OutputArgConcatenationWithLiteralError) {
  // A concatenation is a valid lvalue only when every element is assignable;
  // a literal element cannot appear on the left of a procedural assignment, so
  // the concatenation is not a valid output actual.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  function void get(output logic [7:0] o);\n"
      "    o = 8'hAB;\n"
      "  endfunction\n"
      "  initial get({a, 4'd5});\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'o' requires a variable", 6,
                            "13.5"));
}

TEST(SubroutineCallElaboration, OutputArgBinaryExprError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a, b;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  initial foo(a + b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'x' requires a variable", 6,
                            "13.5"));
}

TEST(SubroutineCallElaboration, OutputArgPartSelectOk) {
  // §13.5/§10.4: a part-select is a valid procedural-assignment lvalue, so it
  // is an admissible output actual (a distinct syntactic form from a scalar
  // bit-select).
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function void get(output logic [3:0] v);\n"
      "    v = 4'd1;\n"
      "  endfunction\n"
      "  initial get(x[3:0]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaboration, OutputArgMemberSelectOk) {
  // A member select of a packed struct is a valid procedural-assignment lvalue
  // (§10.4) and is therefore an admissible output actual.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } pair_t;\n"
      "  pair_t s;\n"
      "  function void get(output logic [3:0] v);\n"
      "    v = 4'd1;\n"
      "  endfunction\n"
      "  initial get(s.lo);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaboration, InoutArgSelectOk) {
  // The lvalue restriction applies equally to the inout direction: an element
  // select of an unpacked array is a valid inout actual.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:3];\n"
      "  function void bump(inout logic [7:0] io);\n"
      "    io = io + 8'd1;\n"
      "  endfunction\n"
      "  initial bump(arr[0]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.5 restricts an output actual to an expression legal on the left-hand
// side of a procedural assignment and says nothing about where the call
// carrying it stands; A.6.4 makes a subroutine_call_statement a statement_item,
// so every position a statement holds a statement in is a position the report
// is owed at. WalkChildStmtsForCallArgs in
// src/elaborator/elaborator_validate_subroutine_args.cpp had written out eight
// of the thirteen child-statement links Stmt declares, and now takes the list
// from ForEachChildStmt in src/elaborator/elaborator_validate_internal.h. The
// cases below cover one newly reached position each.

// A.6.3's par_block holds a list of statement_or_null between fork and its
// join_keyword, which the parser keeps in Stmt::fork_stmts. §13.4.4 grants a
// fork-join_none written inside a function "any statements that are legal
// within a task", so a call in a fork arm is a call §13.5 governs.
TEST(SubroutineCallElaboration, OutputArgLiteralInForkArmError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  initial fork\n"
      "    foo(42);\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'x' requires a variable", 6,
                            "13.5"));
}

// A.6.3's action_block gives an immediate assertion a statement in each arm,
// held in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(SubroutineCallElaboration, OutputArgLiteralInAssertionPassStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  initial assert (1) foo(42);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'x' requires a variable", 5,
                            "13.5"));
}

TEST(SubroutineCallElaboration, OutputArgLiteralInAssertionFailStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  initial assert (1) else foo(42);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'x' requires a variable", 5,
                            "13.5"));
}

// §18.16's `randcase_item ::= expression : statement_or_null` puts a statement
// after each weight, held in Stmt::randcase_items.
TEST(SubroutineCallElaboration, OutputArgLiteralInRandcaseItemError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  initial randcase\n"
      "    1 : foo(42);\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'x' requires a variable", 6,
                            "13.5"));
}

// A.6.12's rs_code_block holds procedural statements, which the parser keeps in
// RsProd::code_stmts under Stmt::rs_productions.
TEST(SubroutineCallElaboration, OutputArgLiteralInRandsequenceCodeBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { foo(42); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'x' requires a variable", 7,
                            "13.5"));
}

// §18.17.1 admits a code block after a rule's weight specification, kept in
// RsRule::weight_code. That is a second statement list under
// Stmt::rs_productions, reached by a different member from the case above.
TEST(SubroutineCallElaboration,
     OutputArgLiteralInRandsequenceWeightCodeBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void foo(output int x);\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  int y;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { foo(42); };\n"
      "      alt : { y = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'x' requires a variable", 8,
                            "13.5"));
}

}  // namespace
