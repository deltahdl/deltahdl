#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ArrayLiteralElaboration, SimpleArrayOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[1:0] = '{10, 20};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, NestedBracesOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct { int a; int b; } ms_t;\n"
             "  ms_t ms[1:0] = '{'{0, 0}, '{1, 1}};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, DefaultKeyOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] arr [0:3];\n"
             "  initial arr = '{default: 8'd0};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, SizeMismatchError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int arr[1:0] = '{10, 20, 30};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 3 elements, but array "
                            "dimension requires 2",
                            2, "10.9.1"));
}

TEST(ArrayLiteralElaboration, FlatInitIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a; int b; } ms_t;\n"
      "  ms_t ms[1:0] = '{0, 0, 1, 1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 4 elements, but array "
                            "dimension requires 2",
                            3, "10.9.1"));
}

TEST(ArrayLiteralElaboration, DuplicateIndexError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  int arr[0:2] = '{0: 1, 1: 2, 0: 3};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate index key '0' in array pattern", 2,
                            "10.9.1"));
}

TEST(ArrayLiteralElaboration, ReplicationOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[0:2] = '{3{0}};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, IndexKeyOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[0:2] = '{0: 10, 1: 20, 2: 30};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, PositionalArrayElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [3];\n"
      "  initial arr = '{1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayLiteralElaboration, NarrowToWideElementOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[0:1] = '{1'b1, 1'b1};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, TypeKeyArrayOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[0:2] = '{int: 42};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, KeyedPatternUncoveredElementError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int arr[0:2] = '{0: 10, 2: 30};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "keyed array pattern does not cover all elements",
                            2, "10.9.1"));
}

// §10.9.1: an item is evaluated in the assignment context of its element, so a
// value that fits the element needs no size warning even when the literal's
// self-determined width differs. A plain integer narrowing into a 1-bit element
// elaborates cleanly.
TEST(ArrayLiteralElaboration, BitElementNoSizeWarning) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  bit arr[1:0] = '{1, 1};\n"
             "endmodule\n"));
}

// §10.9.1 requires every element of an assignment pattern targeting an
// unpacked array to be of the array's element type, and conditions that on the
// assignment rather than on the statement the assignment is written in. An
// array-typed item is illegal wherever the assignment stands.
//
// ElaboratorOperationRules::WalkStmtsForArrayPatternElemType in
// src/elaborator/elaborator_validate_operations_arrays.cpp reached six of the
// thirteen statement links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states. The seven cases here
// each put `A2 = '{A3, A3}` in one of the seven positions it did not read,
// every one of which elaborated clean beforehand.
//
// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword [ :
// block_identifier ]`, so a fork arm is a statement position like any other.
TEST(ArrayLiteralElaboration, ArrayItemInPatternInAForkArmNames10_9_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A2[1:2];\n"
      "  initial begin\n"
      "    fork\n"
      "      A2 = '{A3, A3};\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern", 7,
                            "10.9.1"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case covers
// the pass arm and the one below it the fail arm.
TEST(ArrayLiteralElaboration,
     ArrayItemInPatternInAnAssertionPassStatementNames10_9_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A2[1:2];\n"
      "  logic ok;\n"
      "  initial assert (ok) A2 = '{A3, A3};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern", 6,
                            "10.9.1"));
}

TEST(ArrayLiteralElaboration,
     ArrayItemInPatternInAnAssertionFailStatementNames10_9_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A2[1:2];\n"
      "  logic ok;\n"
      "  initial assert (ok) else A2 = '{A3, A3};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern", 6,
                            "10.9.1"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. The rule
// is a static one, so it holds whether the weighted draw would select the item
// or not.
TEST(ArrayLiteralElaboration, ArrayItemInPatternInARandcaseItemNames10_9_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A2[1:2];\n"
      "  initial randcase 1: A2 = '{A3, A3}; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern", 5,
                            "10.9.1"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions.
TEST(ArrayLiteralElaboration,
     ArrayItemInPatternInARandsequenceCodeBlockNames10_9_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A2[1:2];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { A2 = '{A3, A3}; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern", 7,
                            "10.9.1"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments |
// for_variable_declaration { , for_variable_declaration }` and
// `for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call`. A.6.2 gives `variable_assignment ::=
// variable_lvalue = expression` and `operator_assignment ::= variable_lvalue
// assignment_operator expression`, whose assignment_operator includes `=`, so
// an assignment stands at each of the two positions: this case writes one at
// the initialization and the case below it writes one at the step.
TEST(ArrayLiteralElaboration,
     ArrayItemInPatternInAForLoopInitializationNames10_9_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A2[1:2];\n"
      "  int i;\n"
      "  initial for (A2 = '{A3, A3}; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern", 6,
                            "10.9.1"));
}

TEST(ArrayLiteralElaboration, ArrayItemInPatternInAForLoopStepNames10_9_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A2[1:2];\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; A2 = '{A3, A3}) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern", 6,
                            "10.9.1"));
}

}  // namespace
