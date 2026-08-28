// §9.2.2.2 "Combinational logic always_comb procedure", the multiple-driver
// rule where the procedure reaches the second driver through a function it
// calls and the call is written somewhere other than a right-hand side. The
// clause says of the variables an always_comb assigns that they "shall not be
// assigned by any other process", and that this "includes variables assigned
// within functions called by the procedure but not those assigned within tasks
// called by the procedure". It puts no condition on where in the procedure the
// call stands, so every case here names one position a statement or an
// expression holds an expression in and asserts the same report.
//
// The cases where the call is written where a call is usually written are in
// test_elaborator_subclause_09_02_02_02a.cpp, which the 1000-line cap in
// .github/workflows/deltahdl.yml separated this file from.

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

}  // namespace
