#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The one report §7.7's rule is made through, named once so that each case
// below reads as the position it covers rather than as a restatement of the
// sentence. ReportedError matches it as a substring, and no other report
// deltahdl makes contains it.
constexpr std::string_view kDpiOpenArrayReport =
    "a dynamic array or queue cannot be passed to the open-array output "
    "argument of DPI import 'f'";

TEST(ArraySubroutineArgValidation, TaskWithMultipleArrayArgsElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  task copy(input int src[4], output int dst[4]);\n"
             "    dst = src;\n"
             "  endtask\n"
             "endmodule\n"));
}

TEST(ArraySubroutineArgValidation, ArrayArgCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[4];\n"
             "  int result;\n"
             "  function int first(int a[4]);\n"
             "    return a[0];\n"
             "  endfunction\n"
             "  initial result = first(arr);\n"
             "endmodule\n"));
}

TEST(ArraySubroutineArgValidation, DynamicArrayArgCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[];\n"
             "  int result;\n"
             "  function int first(int a[]);\n"
             "    return a[0];\n"
             "  endfunction\n"
             "  initial result = first(d);\n"
             "endmodule\n"));
}

// A dynamic array may be bound to a fixed-size formal: the equal-size
// requirement is checked at run time, so elaboration accepts the association.
TEST(ArraySubroutineArgValidation, DynamicActualToFixedFormalCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[];\n"
             "  int result;\n"
             "  function int first(int a[4]);\n"
             "    return a[0];\n"
             "  endfunction\n"
             "  initial result = first(d);\n"
             "endmodule\n"));
}

// A formal that accepts a dynamic array may be passed a fixed-size array of a
// compatible type; elaboration accepts the association.
TEST(ArraySubroutineArgValidation, FixedActualToDynamicFormalCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[4];\n"
             "  int result;\n"
             "  function int first(int a[]);\n"
             "    return a[0];\n"
             "  endfunction\n"
             "  initial result = first(arr);\n"
             "endmodule\n"));
}

// A dynamic array passed to a DPI import's open-array (unsized) output formal
// is illegal: the unsized dimension leaves the C side no fixed element count to
// write back into.
TEST(ArraySubroutineArgValidation, DpiOpenArrayOutputRejectsDynamicArray) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial f(dyn);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

// §7.7 phrases the prohibition as an "output direction mode", which an inout
// formal also has: an inout open-array DPI formal likewise cannot receive a
// dynamic array actual, so this association is rejected just like the output
// one.
TEST(ArraySubroutineArgValidation, DpiOpenArrayInoutRejectsDynamicArray) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(inout int a[]);\n"
      "  int dyn[];\n"
      "  initial f(dyn);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

// A queue is rejected for the same open-array output formal.
TEST(ArraySubroutineArgValidation, DpiOpenArrayOutputRejectsQueue) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int q[$];\n"
      "  initial f(q);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

// The prohibition is specific to the output direction: a dynamic array is a
// legal actual for an open-array input formal.
TEST(ArraySubroutineArgValidation, DpiOpenArrayInputAcceptsDynamicArray) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  import \"DPI-C\" function void f(input int a[]);\n"
             "  int dyn[];\n"
             "  initial f(dyn);\n"
             "endmodule\n"));
}

// A fixed-size array remains a legal actual for an open-array output formal;
// only dynamic arrays and queues are prohibited.
TEST(ArraySubroutineArgValidation, DpiOpenArrayOutputAcceptsFixedArray) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  import \"DPI-C\" function void f(output int a[]);\n"
             "  int fixed[4];\n"
             "  initial f(fixed);\n"
             "endmodule\n"));
}

// §7.7's prohibition is on a DPI import call and puts no condition on where
// that call stands, so every position a statement holds a statement in is a
// position the report is made at. Elaborator::WalkStmtsForDpiArgs in
// src/elaborator/elaborator_validate_subroutine.cpp had written out six of the
// thirteen child-statement links Stmt declares, and now takes the list from
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h. The cases
// below cover one newly reached position each.

// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword`, whose
// statements the parser keeps in Stmt::fork_stmts.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInForkBranch) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial fork\n"
      "    f(dyn);\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

// A.6.8 makes a for_initialization a list of variable_assignments, each of
// whose right-hand expressions may be a function call. The parser keeps them in
// Stmt::for_inits, one blocking-assignment statement per control variable.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInForInitialization) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  int r;\n"
      "  initial for (int i = f(dyn); i < 1; i = i + 1) r = i;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

// A.6.8's `for_step_assignment ::= operator_assignment | inc_or_dec_expression
// | function_subroutine_call` admits a call outright, so the header's third
// slot holds one. The parser keeps it in Stmt::for_steps.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInForStep) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int dyn[];\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; f(dyn)) i = i + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInAssertionPassStatement) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial assert (1) f(dyn);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInAssertionFailStatement) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial assert (1) else f(dyn);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, kept in
// Stmt::randcase_items.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandcaseItem) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial randcase\n"
      "    1 : f(dyn);\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceCodeBlock) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { f(dyn); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceWeightCodeBlock) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int dyn[];\n"
      "  int i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { f(dyn); };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 7, "7.7"));
}

// §7.7 puts no condition on where the prohibited call stands inside an
// expression either: A.8.4 makes a function_subroutine_call a primary, so the
// report is owed at every position a statement holds an expression in.
// Elaborator::WalkStmtsForDpiArgs had read Stmt::rhs, Stmt::expr and
// Stmt::condition alone, and now takes the list from ForEachChildExpr in
// src/elaborator/elaborator_validate_internal.h. The cases below cover one
// newly reached expression position each.
//
// Stmt::wait_order_events is the one position with no case: A.6.5 gives
// `wait_order ( hierarchical_identifier { , hierarchical_identifier } )
// action_block`, which admits no expression and so no call.

// A.8.5's `variable_lvalue ::= [ implicit_class_handle . | package_scope ]
// hierarchical_variable_identifier select` reaches an expression through the
// bit select A.8.4's `select` admits, so a call stands in the left-hand side of
// an assignment, kept in Stmt::lhs.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInAssignmentLvalueSelect) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  int arr[4];\n"
      "  initial arr[f(dyn)] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

// A.6.5's `delay_control ::= # delay_value | # ( mintypmax_expression )` admits
// an expression in its parenthesized form, kept in Stmt::delay.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInDelayControl) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial #(f(dyn)) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

// A.6.11's `cycle_delay ::= ## integral_number | ## identifier | ##
// ( expression )` admits an expression in its parenthesized form, kept in
// Stmt::cycle_delay.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInCycleDelay) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial ##(f(dyn)) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

// A.6.8's `for ( [ for_initialization ] ; [ expression ] ; [ for_step ] )`
// puts an expression between the two semicolons, kept in Stmt::for_cond. This
// is one of the two positions #3303 named.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInForCondition) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  int i;\n"
      "  initial for (i = 0; f(dyn) < 1; i = i + 1) i = i;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

// A.6.10's `simple_immediate_assert_statement ::= assert ( expression )
// action_block` puts an expression in the parentheses, kept in
// Stmt::assert_expr. This is the second of the two positions #3303 named.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInAssertionExpression) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial assert (f(dyn) == 0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

// A.6.5's `delay_or_event_control ::= ... | repeat ( expression )
// event_control` counts the events with an expression, kept in
// Stmt::repeat_event_count.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRepeatEventCount) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  int r;\n"
      "  logic clk;\n"
      "  initial r = repeat (f(dyn)) @(posedge clk) 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

// A.2.4's `variable_decl_assignment ::= variable_identifier
// { variable_dimension } [ = expression ]` gives a declaration an initializer,
// kept in Stmt::var_init when the declaration stands in a block.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInBlockVariableInitializer) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    int r = f(dyn);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

// A.6.5's `event_expression ::= [ edge_identifier ] expression
// [ iff expression ]` opens with an expression, kept in EventExpr::signal for
// each entry of Stmt::events.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInEventExpression) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial @(f(dyn)) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

// The same production's `iff expression` is a second expression, kept in
// EventExpr::iff_condition, which the walk reaches separately from
// EventExpr::signal.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInEventIffCondition) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  logic clk;\n"
      "  initial @(posedge clk iff f(dyn)) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

// §18.16's `randcase_item ::= expression : statement_or_null` weights the item
// with an expression, kept as the first of each Stmt::randcase_items pair. The
// case above for the item's body covers the second.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandcaseWeight) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  int r;\n"
      "  initial randcase\n"
      "    f(dyn) : r = 1;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

// A.6.7's `case_item ::= case_item_expression { , case_item_expression } :
// statement_or_null` labels the item with expressions, kept in
// CaseItem::patterns for each entry of Stmt::case_items.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInCaseItemExpression) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  int r;\n"
      "  initial case (r)\n"
      "    f(dyn) : r = 1;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

// A.2.5's `unpacked_dimension ::= [ constant_range ] | [ constant_expression ]`
// sizes a declaration with an expression, kept in Stmt::var_unpacked_dims when
// the declaration stands in a block. A.8.2 gives `constant_function_call ::=
// function_subroutine_call`, so the grammar reaches a call here; the source
// below breaks that footnote's requirement of a constant function as well, and
// §7.7's report is owed at the position whichever other rule the source also
// breaks.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInUnpackedDimension) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    int a[f(dyn)];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

// A.6.12's `rs_weight_specification ::= integral_number | ps_identifier |
// ( expression )` admits an expression in its parenthesized form, kept in
// RsRule::weight.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceWeightExpression) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : one := (f(dyn));\n"
      "      one : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

// A.6.12's `rs_production_list ::= ... | rand join [ ( expression ) ]
// rs_production_item rs_production_item { rs_production_item }` admits an
// expression before the item list, kept in RsRule::rand_join_expr.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceRandJoinExpression) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : rand join (f(dyn)) one two;\n"
      "      one : { ; };\n"
      "      two : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

// The same production's items are rs_production_items, and A.6.12 gives
// `rs_production_item ::= rs_production_identifier [ ( list_of_arguments ) ]`,
// so each carries actual arguments. They are kept in
// RsRule::rand_join_items[].args.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceRandJoinItemArgument) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : rand join one(f(dyn)) two;\n"
      "      void one(int x) : { ; };\n"
      "      two : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

// A.6.12's `rs_prod ::= rs_production_item | ...` makes a plain item a
// production of its own, whose arguments are kept in RsProd::item.args.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceItemArgument) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : one(f(dyn));\n"
      "      void one(int x) : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

// A.6.12's `rs_if_else ::= if ( expression ) rs_production_item [ else
// rs_production_item ]` tests an expression, kept in RsProd::condition.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceIfCondition) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if (f(dyn)) one;\n"
      "      one : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

// The same production's then-item carries its own arguments, kept in
// RsProd::if_true.args.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceIfBranchArgument) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if (1) one(f(dyn));\n"
      "      void one(int x) : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

// Its else-item is a third list, kept in RsProd::if_false.args, which the
// walk reaches separately from RsProd::if_true.args.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceElseBranchArgument) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if (1) one(0) else one(f(dyn));\n"
      "      void one(int x) : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

// A.6.12's `rs_repeat ::= repeat ( expression ) rs_production_item` counts the
// repetitions with an expression, kept in RsProd::repeat_count.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceRepeatCount) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : repeat (f(dyn)) one;\n"
      "      one : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

// The item that production repeats carries its own arguments, kept in
// RsProd::repeat_item.args.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceRepeatItemArgument) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : repeat (1) one(f(dyn));\n"
      "      void one(int x) : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

// A.6.12's `rs_case ::= case ( case_expression ) rs_case_item { rs_case_item }
// endcase` selects on an expression, kept in RsProd::case_expr.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceCaseExpression) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (f(dyn)) 0 : one; endcase;\n"
      "      one : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

// A.6.12's `rs_case_item ::= case_item_expression { , case_item_expression } :
// rs_production_item ;` labels the arm with expressions, kept in
// RsProd::case_items[].patterns.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceCaseItemExpression) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (0) f(dyn) : one; endcase;\n"
      "      one : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

// The arm's own rs_production_item carries arguments, kept in
// RsProd::case_items[].item.args.
TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceCaseItemArgument) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (0) 0 : one(f(dyn)); endcase;\n"
      "      void one(int x) : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

}  // namespace
