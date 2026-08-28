// §9.2.2.2 "Combinational logic always_comb procedure", in the two families of
// case the 1000-line cap in .github/workflows/deltahdl.yml kept out of
// test_elaborator_subclause_09_02_02_02a.cpp.
//
// The first is the multiple-driver rule where the procedure reaches the second
// driver through a function it calls and the call is written somewhere other
// than a right-hand side. The clause says of the variables an always_comb
// assigns that they "shall not be assigned by any other process", and that this
// "includes variables assigned within functions called by the procedure but not
// those assigned within tasks called by the procedure". It puts no condition on
// where in the procedure the call stands, so every case in that family names
// one position a statement or an expression holds an expression in and asserts
// the same report. The cases where the call is written where a call is usually
// written are in test_elaborator_subclause_09_02_02_02a.cpp.
//
// The second is the latch-inference warning the clause asks for -- "warn if the
// behavior within an always_comb procedure does not represent combinational
// logic, such as if latched behavior can be inferred" -- read at one statement
// position each. Those cases begin below the multiple-driver ones.

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// CollectCallNamesStmt in src/elaborator/elaborator_process.cpp is what finds
// the calls a procedure makes, and CollectFuncLhsPrefixes beside it opens the
// functions they name and adds what those assign to the procedure's own
// targets. A call the walk does not reach leaves the function unopened, so
// every variable it assigns stays out of the procedure's set and the source
// built here elaborates clean with `y` assigned by an always_comb and by an
// initial procedure at once.
//
// The call is the only route by which `y` reaches the always_comb's target set.
// No `stmt` below assigns `y`, so the walk over the procedure's own assignment
// targets cannot account for the report.
//
// The report stands at the always_comb, and the line is read back out of the
// source rather than counted so that it stays right if the preamble is edited.
void ExpectFunctionTargetDrivenTwice(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n"
      "  logic a, y, z, ok;\n"
      "  logic [3:0] w;\n"
      "  int arr[4];\n"
      "  int q[$];\n"
      "  function automatic logic f();\n"
      "    y = a;\n"
      "    return a;\n"
      "  endfunction\n"
      "  always_comb\n"
      "    " +
      stmt +
      "\n"
      "  initial y = a;\n"
      "endmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "variable 'y' driven by always_comb and another process",
                    LineHolding(src, "always_comb"), "9.2.2.2"));
}

// The statements a statement holds a statement in. ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states those thirteen links,
// and CollectCallNamesStmt had written out nine of them, so a call in one of
// the other four was never seen.

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each. §9.2.2.2 puts no condition on when the call runs, so
// the arm the assertion would take is not the question.
TEST(AlwaysCombMultiDriver, FunctionCalledFromAnAssertionPassStmtIsADriver) {
  ExpectFunctionTargetDrivenTwice("assert (ok) z = f();");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromAnAssertionFailStmtIsADriver) {
  ExpectFunctionTargetDrivenTwice("assert (ok) else z = f();");
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. The weighted draw picks an item while the design runs; the
// single-driver rule is decided before it does, so a call in an item counts
// whether the item would be selected or not.
TEST(AlwaysCombMultiDriver, FunctionCalledFromARandcaseItemIsADriver) {
  ExpectFunctionTargetDrivenTwice("randcase 1: z = f(); endcase");
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(AlwaysCombMultiDriver, FunctionCalledFromARandsequenceCodeBlockIsADriver) {
  ExpectFunctionTargetDrivenTwice(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { z = f(); };\n"
      "      endsequence\n"
      "    end");
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second statement list
// under Stmt::rs_productions, reached by a different member from
// RsProd::code_stmts, so the case above does not answer for it.
TEST(AlwaysCombMultiDriver,
     FunctionCalledFromARandsequenceWeightCodeBlockIsADriver) {
  ExpectFunctionTargetDrivenTwice(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { z = f(); };\n"
      "        alt : { z = a; };\n"
      "      endsequence\n"
      "    end");
}

// The positions a statement holds an expression in. ForEachChildExpr in
// src/elaborator/elaborator_validate_internal.h states those sixteen, and
// CollectCallNamesStmt had written out four of them -- Stmt::expr, Stmt::rhs,
// Stmt::condition and Stmt::for_cond -- so each case below elaborated clean
// before the walk took its list from ForEachChildExpr.
//
// Stmt::wait_order_events has no case here, and that is a fact about the
// grammar rather than a gap. A.6.5 gives `wait_order ( hierarchical_identifier
// { , hierarchical_identifier } ) action_block`, whose operands are identifiers
// and not expressions, so no conforming source writes a call in one.

// §6.21 lets a block declare a variable, and the parser puts such a
// declaration's initializer in Stmt::var_init.
TEST(AlwaysCombMultiDriver, FunctionCalledFromABlockVarInitializerIsADriver) {
  ExpectFunctionTargetDrivenTwice(
      "begin\n"
      "      int r = f();\n"
      "      z = a;\n"
      "    end");
}

// §11.5.1 makes the index of a bit-select an expression, and it stays an
// expression when the select is the target of the assignment: the parser puts
// the whole select in Stmt::lhs with the index beneath it.
TEST(AlwaysCombMultiDriver, FunctionCalledFromAnAssignmentTargetIsADriver) {
  ExpectFunctionTargetDrivenTwice("w[f()] = a;");
}

// §9.2.2.2 shows `d <= #1ns b & c;` as a legal always_comb body, so an
// intra-assignment delay is a position the clause itself puts a call's reach
// in. §9.4.5 admits a general expression as the delay, which the parser keeps
// in Stmt::delay.
TEST(AlwaysCombMultiDriver, FunctionCalledFromAnIntraAssignmentDelayIsADriver) {
  ExpectFunctionTargetDrivenTwice("z <= #(f()) a;");
}

// §14.11 writes a cycle delay as `## expression`, which the parser keeps in
// Stmt::cycle_delay rather than in Stmt::delay.
TEST(AlwaysCombMultiDriver,
     FunctionCalledFromAnIntraAssignmentCycleDelayIsADriver) {
  ExpectFunctionTargetDrivenTwice("z <= ##(f()) a;");
}

// A.6.5 gives `event_expression ::= [ edge_identifier ] expression [ iff
// expression ]`, so an event control holds two expressions per event. The
// parser keeps them in EventExpr::signal and EventExpr::iff_condition, and this
// case and the next cover one each.
TEST(AlwaysCombMultiDriver, FunctionCalledFromAnEventExpressionIsADriver) {
  ExpectFunctionTargetDrivenTwice("z <= @(f()) a;");
}

TEST(AlwaysCombMultiDriver, FunctionCalledFromAnEventIffConditionIsADriver) {
  ExpectFunctionTargetDrivenTwice("z <= @(posedge a iff f()) 1'b1;");
}

// §9.4.5 gives the repeat form of an intra-assignment control a count of its
// own, which the parser keeps in Stmt::repeat_event_count. The count decides
// how many events the assignment waits for while the design runs; the
// single-driver rule is decided before it does.
TEST(AlwaysCombMultiDriver, FunctionCalledFromARepeatEventCountIsADriver) {
  ExpectFunctionTargetDrivenTwice("z <= repeat (f()) @(posedge a) 1'b1;");
}

// §16.3 gives `simple_immediate_assert_statement ::= assert ( expression )
// action_block`. The asserted expression is kept in Stmt::assert_expr, which is
// a different member from the Stmt::condition an if statement uses, so the two
// arm cases above do not answer for it.
TEST(AlwaysCombMultiDriver, FunctionCalledFromAnAssertedExpressionIsADriver) {
  ExpectFunctionTargetDrivenTwice("assert (f());");
}

// §12.5 gives `case_item ::= case_item_expression { , case_item_expression } :
// statement_or_null`, so an arm's pattern is an expression of its own, kept in
// the patterns of a Stmt::case_items entry.
TEST(AlwaysCombMultiDriver, FunctionCalledFromACaseItemPatternIsADriver) {
  ExpectFunctionTargetDrivenTwice(
      "case (a)\n"
      "      f(): z = 1'b1;\n"
      "      default: z = 1'b0;\n"
      "    endcase");
}

// §18.16 makes the weight of a randcase item an expression, kept in the first
// member of a Stmt::randcase_items entry. The case above covers the statement
// under the same entry, which is a different member and a different walk.
TEST(AlwaysCombMultiDriver, FunctionCalledFromARandcaseWeightIsADriver) {
  ExpectFunctionTargetDrivenTwice("randcase f(): z = a; endcase");
}

// A.2.5 gives `unpacked_dimension ::= [ constant_range ] | [
// constant_expression ]` and A.8.2 admits a constant_function_call as a
// constant primary, so a declaration in a block can size an array from a call.
// The parser keeps such a dimension in Stmt::var_unpacked_dims.
TEST(AlwaysCombMultiDriver,
     FunctionCalledFromABlockUnpackedDimensionIsADriver) {
  ExpectFunctionTargetDrivenTwice(
      "begin\n"
      "      int u[f()];\n"
      "      z = a;\n"
      "    end");
}

// The positions an expression holds an expression in. AnyExprChild in
// src/elaborator/elaborator_validate_internal.h states those thirteen, and
// CollectCallNamesExpr had written out nine of them. The four cases below fail
// even under a fix that only widens the statement walk, because each call
// stands under Stmt::rhs, which that walk already read.

// §11.5.1 gives a part-select two bounds. The parser keeps the first in
// Expr::index, which the walk already read, and the second in Expr::index_end,
// which it did not.
TEST(AlwaysCombMultiDriver, FunctionCalledFromAPartSelectUpperBoundIsADriver) {
  ExpectFunctionTargetDrivenTwice("z = w[3:f()];");
}

// §7.12.1 gives an array reduction method a `with` clause, whose expression the
// parser keeps in Expr::with_expr on the call node rather than among its
// arguments.
TEST(AlwaysCombMultiDriver, FunctionCalledFromAWithClauseIsADriver) {
  ExpectFunctionTargetDrivenTwice("z = q.sum() with (f());");
}

// A.8.1 gives `multiple_concatenation ::= { constant_expression concatenation
// }`, whose count the parser keeps in Expr::repeat_count. The concatenation it
// multiplies goes in Expr::elements, which the walk already read.
TEST(AlwaysCombMultiDriver, FunctionCalledFromAReplicationCountIsADriver) {
  ExpectFunctionTargetDrivenTwice("z = {f(){1'b0}};");
}

// §10.9's array_pattern_key is a constant_expression, so an assignment
// pattern's key is an expression of its own. The parser keeps it in
// Expr::pattern_keys, beside the value it names in Expr::elements.
TEST(AlwaysCombMultiDriver, FunctionCalledFromAnAssignmentPatternKeyIsADriver) {
  ExpectFunctionTargetDrivenTwice("arr = '{f(): 1};");
}

// §9.2.2.2's latch-inference warning, per statement position. InfersLatch in
// src/elaborator/elaborator_process.cpp answers it from two walks over the
// procedure body: CollectAssignedVariables gathers every variable the body
// assigns anywhere, and AssignedOnEveryPath gathers those an execution of the
// body cannot leave unassigned. A variable in the first set and not the second
// keeps its previous value on the paths that skip it, which is what a latch
// does.
//
// Both walks named six of the thirteen statement links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states, so a variable assigned
// only in a fork arm, a for header, a randcase item, an assertion action block
// or a randsequence code block was in neither set and the warning could not
// reach it. Each case below names one position, and says which of the two
// answers the position gives.

// §16.3 has the pass statement of an action block "executed if the expression
// evaluates to true", so a variable assigned only there is left holding its
// previous value whenever the assertion fails. It is assigned somewhere and on
// no path, which is the latch.
TEST(AlwaysCombLatchWarning, AssertionPassStatementAssignmentInfersLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb assert (a) y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "always_comb may infer latched behavior", 3,
                              "9.2.2.2"));
}

// The fail statement is the other arm of the same action block, kept in a
// different member of Stmt, and §16.3 has it "executed if the expression
// evaluates to false".
TEST(AlwaysCombLatchWarning, AssertionFailStatementAssignmentInfersLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb assert (a) else y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "always_comb may infer latched behavior", 3,
                              "9.2.2.2"));
}

// Both arms written is still a latch, and this is the case that says so. §16.3
// alone would make the two arms a two-way choice on the assertion expression,
// covering its whole domain the way an if with an else covers a condition's,
// and an every-path answer built on §16.3 alone would report no latch here. But
// §20.11 gives $assertcontrol "the capability to enable/disable action block
// execution of assertions and expect statements", so there is a way through the
// statement that runs neither arm and leaves `y` holding its previous value.
TEST(AlwaysCombLatchWarning, AssertionBothActionArmsStillInferLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb assert (a) y = a; else y = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "always_comb may infer latched behavior", 3,
                              "9.2.2.2"));
}

// §18.16 rules that "if all randcase_items specify zero weights, then no branch
// is taken", and that the weights "can be arbitrary expressions", read while
// the design runs. So no item of a randcase is reached on every path through
// it, however many items are written, and a variable assigned only in one is
// latched.
TEST(AlwaysCombLatchWarning, RandcaseItemAssignmentInfersLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb randcase 1: y = a; endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "always_comb may infer latched behavior", 3,
                              "9.2.2.2"));
}

// §18.17 rules that production lists separated by a "|" "imply a set of
// choices, which the generator will make at random", so a randsequence code
// block is reached at the generator's discretion. A.6.12 gives `rs_code_block
// ::= { { data_declaration } { statement_or_null } }`, whose statements the
// parser keeps in RsProd::code_stmts under Stmt::rs_productions.
TEST(AlwaysCombLatchWarning, RandsequenceCodeBlockAssignmentInfersLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb\n"
      "    randsequence(main)\n"
      "      main : { y = a; };\n"
      "    endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "always_comb may infer latched behavior", 3,
                              "9.2.2.2"));
}

// §9.3.2's Table 9-1 has join_none leave "the parent process ... to execute
// concurrently with all the processes spawned by the fork", so an arm's
// assignment need not have been made when control passes out of the block and
// the fork puts nothing on every path. The fork-join is also barred from an
// always_comb by §9.2.2.2.2 and reported separately; this case is about the
// warning, and the counterpart that does complete every arm is in
// test_elaborator_subclause_09_02_02_03.cpp.
TEST(AlwaysCombLatchWarning, ForkJoinNoneArmAssignmentInfersLatch) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb fork y = a; join_none\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "always_comb may infer latched behavior", 3,
                              "9.2.2.2"));
}

// The other direction, at the two positions of a for header. §12.7.1 step a)
// "executes one or more for_initialization assignments" once and under no
// condition, so a variable initialized there is assigned on every path through
// the loop however the body is written. `y` is assigned nowhere else
// unconditionally -- the body's if has no else -- so the initialization is the
// whole of the answer, and a walk that skipped it would warn about a procedure
// that describes combinational logic.
TEST(AlwaysCombLatchWarning, ForInitializationAssignmentIsCombinational) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic sel, a, y;\n"
      "  int i;\n"
      "  always_comb begin\n"
      "    for (y = 1'b0; i < 2; i++)\n"
      "      if (sel) y = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §12.7.1 step c) "executes one or more for_step assignments ... then repeats
// step b)", so a step assignment is made once the body has run, which this
// check counts as taken for the reason it counts any loop body as taken. The
// initialization is omitted here, which A.6.8 permits, so the step is the only
// position that can put `y` on every path.
TEST(AlwaysCombLatchWarning, ForStepAssignmentIsCombinational) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic sel, a, y;\n"
      "  int i;\n"
      "  always_comb begin\n"
      "    for ( ; i < 2; i++, y = a)\n"
      "      if (sel) y = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
