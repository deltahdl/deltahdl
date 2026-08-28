#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a dynamic array or queue cannot be passed to the "
                            "open-array output argument of DPI import 'f'",
                            4, "7.7"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a dynamic array or queue cannot be passed to the "
                            "open-array output argument of DPI import 'f'",
                            4, "7.7"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a dynamic array or queue cannot be passed to the "
                            "open-array output argument of DPI import 'f'",
                            4, "7.7"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a dynamic array or queue cannot be passed to the "
                            "open-array output argument of DPI import 'f'",
                            5, "7.7"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a dynamic array or queue cannot be passed to the "
                            "open-array output argument of DPI import 'f'",
                            5, "7.7"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a dynamic array or queue cannot be passed to the "
                            "open-array output argument of DPI import 'f'",
                            5, "7.7"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a dynamic array or queue cannot be passed to the "
                            "open-array output argument of DPI import 'f'",
                            4, "7.7"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a dynamic array or queue cannot be passed to the "
                            "open-array output argument of DPI import 'f'",
                            4, "7.7"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a dynamic array or queue cannot be passed to the "
                            "open-array output argument of DPI import 'f'",
                            5, "7.7"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a dynamic array or queue cannot be passed to the "
                            "open-array output argument of DPI import 'f'",
                            6, "7.7"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a dynamic array or queue cannot be passed to the "
                            "open-array output argument of DPI import 'f'",
                            7, "7.7"));
}

}  // namespace
