#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// 18.5.11: a function called from a constraint may take input arguments. With
// only input formals the call is legal.
TEST(FunctionsInConstraints, InputArgumentFunctionAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a); return a; endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: a function used in a constraint shall not have output arguments.
TEST(FunctionsInConstraints, OutputArgumentFunctionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(output int a); a = 1; return a; endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'f' used in a constraint shall not have "
                            "output, inout, or non-const ref arguments",
                            5, "18.5.11"));
}

// 18.5.11: a function used in a constraint shall not have inout arguments.
TEST(FunctionsInConstraints, InoutArgumentFunctionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(inout int a); return a; endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'f' used in a constraint shall not have "
                            "output, inout, or non-const ref arguments",
                            5, "18.5.11"));
}

// 18.5.11: a non-const ref argument is also forbidden in a constraint function,
// since the call could write back into a variable through the reference.
TEST(FunctionsInConstraints, NonConstRefArgumentFunctionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(ref int a); return a; endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'f' used in a constraint shall not have "
                            "output, inout, or non-const ref arguments",
                            5, "18.5.11"));
}

// 18.5.11: a const ref argument is expressly allowed, so a constraint function
// taking one is accepted.
TEST(FunctionsInConstraints, ConstRefArgumentFunctionAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(const ref int a); return a; endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: the restriction targets functions actually used in a constraint. A
// function with a ref argument that is never called from a constraint is fine.
TEST(FunctionsInConstraints, RefArgumentFunctionNotInConstraintAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function int f(ref int a); return a; endfunction\n"
             "  constraint c1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: a function used in a constraint cannot modify the constraints by
// calling rand_mode(). A constraint function whose body does so is rejected.
TEST(FunctionsInConstraints, ConstraintFunctionCallingRandModeRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a); this.rand_mode(0); return a; "
             "endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    5, "18.5.11"));
}

// 18.5.11: likewise a constraint function shall not call constraint_mode().
TEST(FunctionsInConstraints, ConstraintFunctionCallingConstraintModeRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a); this.constraint_mode(0); return a; "
             "endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    5, "18.5.11"));
}

// 18.5.11: a constraint function that calls neither built-in is fine, so an
// ordinary helper call in its body does not trip the no-modify rule.
TEST(FunctionsInConstraints, ConstraintFunctionWithBenignBodyAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int g(int a); return a + 1; endfunction\n"
             "  function int f(int a); return g(a); endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: the callee is resolved through the class hierarchy, so a function
// inherited from a base class is checked when a derived-class constraint calls
// it. A base function with an output argument is rejected from the derived
// constraint.
TEST(FunctionsInConstraints, BaseClassFunctionWithOutputArgRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function int f(output int a); a = 0; return a; endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'f' used in a constraint shall not have "
                            "output, inout, or non-const ref arguments",
                            7, "18.5.11"));
}

// 18.5.11: the restriction applies to every formal, not just the first. A
// function whose offending argument follows a permitted one is still rejected,
// so the argument scan must look past the leading input argument.
TEST(FunctionsInConstraints, LaterArgumentBadDirectionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a, output int b); b = 0; return a; "
             "endfunction\n"
             "  constraint c1 { x == f(y, x); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'f' used in a constraint shall not have "
                            "output, inout, or non-const ref arguments",
                            5, "18.5.11"));
}

// 18.5.11: a function with no arguments has nothing to forbid, so calling one
// in a constraint is legal — the empty argument list is the boundary of the
// scan.
TEST(FunctionsInConstraints, NoArgumentFunctionAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function int f(); return 7; endfunction\n"
             "  constraint c1 { x == f(); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: the no-modify rule reaches a rand_mode()/constraint_mode() call
// buried inside the function body, not just one at the top level. A call nested
// in a control-flow statement is found by the recursive body scan and rejected.
TEST(FunctionsInConstraints, ModeMethodCallNestedInControlFlowRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    if (a > 0) this.rand_mode(0);\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

// 18.5.11: the restrictions apply to every function called in the constraint,
// including one nested as the argument of another call. An inner function with
// a forbidden output argument is rejected even though the outer call is benign.
TEST(FunctionsInConstraints, NestedConstraintCallInnerFunctionChecked) {
  ElabFixture f;
  EXPECT_FALSE(ElabOk(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  function int inner(output int a); a = 0; return a; endfunction\n"
      "  function int outer(int a); return a; endfunction\n"
      "  constraint c1 { x == outer(inner(y)); }\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'inner' used in a constraint shall not "
                            "have output, inout, or non-const ref arguments",
                            6, "18.5.11"));
}

// 18.5.11 forbids the call anywhere in a function that appears in a
// constraint and names no position it is allowed in. §16.3's action_block puts
// a statement after the asserted expression, which the parser keeps in
// Stmt::assert_pass_stmt; a body walk that omits that field exempts the call
// written there.
TEST(FunctionsInConstraints, ModeMethodCallInAssertionPassStatementRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    assert (a > 0) this.rand_mode(0);\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

// §16.3's action_block also puts a statement after `else`, which the parser
// keeps in Stmt::assert_fail_stmt. 18.5.11 reaches a call written there for the
// same reason it reaches one in the pass statement.
TEST(FunctionsInConstraints, ModeMethodCallInAssertionFailStatementRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    assert (a > 0) else this.constraint_mode(0);\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements and 18.5.11 forbids the call in one as it forbids it in a
// begin-end block.
TEST(FunctionsInConstraints, ModeMethodCallInRandsequenceCodeBlockRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : { this.rand_mode(0); };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    10, "18.5.11"));
}

// A.6.12's `rs_rule ::= rs_production_list [ := weight_specification [
// rs_code_block ] ]` puts a second code block after the weight, which the
// parser keeps in RsRule::weight_code rather than in RsProd::code_stmts. A walk
// that reads only the production's own block leaves this one unreached.
TEST(FunctionsInConstraints, ModeMethodCallInRandsequenceWeightBlockRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : a := 5 { this.constraint_mode(0); };\n"
             "      a : { ; };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    11, "18.5.11"));
}

// A.6.5 gives `delay_control ::= # delay_value | # ( mintypmax_expression )`,
// so a delay control admits a call in its parenthesized form. 18.5.11 names no
// position the call is allowed in, so the one written there is reported like
// any other.
TEST(FunctionsInConstraints, ModeMethodCallInDelayControlRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    #(this.rand_mode(0)) ;\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

// A.6.11's `cycle_delay ::= ## integral_number | ## identifier | ## (
// expression )` admits a call in its third alternative, which the parser keeps
// in Stmt::cycle_delay rather than in Stmt::delay.
TEST(FunctionsInConstraints, ModeMethodCallInCycleDelayRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    ##(this.constraint_mode(0)) ;\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

// 16.3's `assert ( expression ) action_block` puts an expression before the
// action block, which the parser keeps in Stmt::assert_expr. A walk that reads
// the action block alone exempts the call written in the asserted expression
// itself.
TEST(FunctionsInConstraints, ModeMethodCallInAssertedExpressionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    assert (this.rand_mode(0));\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

// A.6.5's `delay_or_event_control ::= ... | repeat ( expression )
// event_control` puts an expression before an intra-assignment event control,
// which the parser keeps in Stmt::repeat_event_count.
TEST(FunctionsInConstraints, ModeMethodCallInRepeatEventCountRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    int b;\n"
             "    b = repeat (this.rand_mode(0)) @(x) a;\n"
             "    return b;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    9, "18.5.11"));
}

// A.6.5 gives `event_expression ::= [ edge_identifier ] expression [ iff
// expression ]`, so the waited-on operand of an event control is an ordinary
// expression, kept in EventExpr::signal for each entry of Stmt::events.
TEST(FunctionsInConstraints, ModeMethodCallInEventControlSignalRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    @(this.rand_mode(0)) ;\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

// The same event_expression admits a second expression after `iff`, which the
// parser keeps in EventExpr::iff_condition. It is a separate member from the
// signal, so a walk that reads the signal alone leaves the call written after
// `iff` unreached.
TEST(FunctionsInConstraints, ModeMethodCallInEventControlIffConditionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    @(x iff this.constraint_mode(0)) ;\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

// A.2.5 gives `unpacked_dimension ::= [ constant_range ] | [
// constant_expression ]`, and A.8.4's constant_primary reaches a
// constant_function_call, so a declaration's unpacked dimension admits a method
// call. The parser keeps it in Stmt::var_unpacked_dims, a member separate from
// the Stmt::var_init a walk over a declaration usually reads.
TEST(FunctionsInConstraints, ModeMethodCallInUnpackedDimensionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    int arr[this.rand_mode(0)];\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    8, "18.5.11"));
}

// A.6.7's case_item puts case_item_expressions before the arm's statement,
// which the parser keeps in CaseItem::patterns. The arm bodies are statements
// the child-statement walk reaches; the guards are expressions it does not.
TEST(FunctionsInConstraints, ModeMethodCallInCaseItemExpressionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    case (a)\n"
             "      this.rand_mode(0) : ;\n"
             "    endcase\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    10, "18.5.11"));
}

// 18.16 gives a randcase item an expression weight before its statement, which
// the parser keeps as the first half of each entry of Stmt::randcase_items.
TEST(FunctionsInConstraints, ModeMethodCallInRandcaseWeightRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randcase\n"
             "      this.rand_mode(0) : ;\n"
             "    endcase\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    10, "18.5.11"));
}

// A.6.12's `rs_weight_specification ::= integral_number | ps_identifier | (
// expression )` admits a call in the weight itself, which the parser keeps in
// RsRule::weight. That is a different member from the RsRule::weight_code the
// block after the weight goes in.
TEST(FunctionsInConstraints, ModeMethodCallInRandsequenceWeightExprRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : a := (this.rand_mode(0));\n"
             "      a : { ; };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    11, "18.5.11"));
}

// A.6.12's `rs_production_list ::= ... | rand join [ ( expression ) ]
// rs_production_item rs_production_item { rs_production_item }` admits a call
// in the expression before the joined productions, which the parser keeps in
// RsRule::rand_join_expr.
TEST(FunctionsInConstraints, ModeMethodCallInRandJoinExpressionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : rand join (this.constraint_mode(0)) a b;\n"
             "      a : { ; };\n"
             "      b : { ; };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    12, "18.5.11"));
}

// A.6.12's `rs_if_else ::= if ( expression ) rs_production_item [ else
// rs_production_item ]` admits a call in the condition, which the parser keeps
// in RsProd::condition.
TEST(FunctionsInConstraints, ModeMethodCallInRandsequenceIfConditionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : if (this.rand_mode(0)) a;\n"
             "      a : { ; };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    11, "18.5.11"));
}

// A.6.12's `rs_repeat ::= repeat ( expression ) rs_production_item` admits a
// call in the repeat count, which the parser keeps in RsProd::repeat_count.
TEST(FunctionsInConstraints, ModeMethodCallInRandsequenceRepeatCountRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : repeat (this.constraint_mode(0)) a;\n"
             "      a : { ; };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    11, "18.5.11"));
}

// A.6.12's `rs_case ::= case ( case_expression ) rs_case_item { rs_case_item }
// endcase` admits a call in the case expression, which the parser keeps in
// RsProd::case_expr.
TEST(FunctionsInConstraints, ModeMethodCallInRandsequenceCaseExprRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : case (this.rand_mode(0)) 0 : a; endcase;\n"
             "      a : { ; };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    11, "18.5.11"));
}

// A.6.12's `rs_case_item ::= case_item_expression { , case_item_expression } :
// rs_production_item ;` puts its own expressions before the arm's production,
// which the parser keeps in RsCaseItem::patterns rather than in
// RsProd::case_expr.
TEST(FunctionsInConstraints, ModeMethodCallInRandsequenceCaseItemExprRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : case (a) this.constraint_mode(0) : b; endcase;\n"
             "      b : { ; };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    11, "18.5.11"));
}

// A.6.12's `rs_production_item ::= rs_production_identifier [ ( list_of_
// arguments ) ]` lets a production be called with actual arguments, which the
// parser keeps in RsProductionItem::args. 18.17.7 gives the production the
// matching tf_port_list.
TEST(FunctionsInConstraints, ModeMethodCallInRandsequenceProdArgRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    randsequence(main)\n"
             "      main : a(this.rand_mode(0));\n"
             "      a(int q) : { ; };\n"
             "    endsequence\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'f' used in a constraint cannot modify the "
                    "constraints by calling rand_mode or constraint_mode",
                    11, "18.5.11"));
}

}  // namespace
