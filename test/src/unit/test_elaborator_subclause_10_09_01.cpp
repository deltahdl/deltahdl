#include <gtest/gtest.h>

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

// The flat pattern for an array of structures breaks §5.10, which has the
// braces of a structure literal nest to reflect the structure, and the §10.9.1
// element count is only a consequence of the flat form, one that would not
// arise for `'{0, 0}`; so the pattern is reported under §5.10 and the count
// says nothing.
TEST(ArrayLiteralElaboration, FlatInitIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a; int b; } ms_t;\n"
      "  ms_t ms[1:0] = '{0, 0, 1, 1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern for an array of structures "
                            "shall nest a pattern per structure",
                            3, "5.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
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

// §10.9.1's type key covers each field whose type matches its type, so a key
// naming a type the elements are not declared with covers nothing: this pattern
// names no element by index, carries no default and matches none by type, which
// the requirement that one of these rules cover every element forbids. The
// coverage check counted any type keyword as covering the whole array and let
// it through, and the simulator then invented a value for all three.
TEST(ArrayLiteralElaboration, TypeKeyThatCannotMatchDoesNotCoverTheArray) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[0:2] = '{int: 8'h05};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "keyed array pattern does not cover all elements",
                            2, "10.9.1"));
}

// The guard on the other direction, beside TypeKeyArrayOk above: a key that
// does match the element type covers every element, and this must stay
// accepted -- it is what keeps the repair from reading every type key as
// covering nothing. §6.22.1 has `byte` match `bit signed [7:0]`, a 2-state
// signed vector of its width over [7:0].
TEST(ArrayLiteralElaboration, TypeKeyMatchingTheElementTypeCoversTheArray) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic arr[0:2] = '{logic: 1'b1};\n"
             "  bit signed [7:0] brr[0:1] = '{byte: 8'h05};\n"
             "endmodule\n"));
}

// §10.9.1 descends into each subarray of the array, applying the same rules and
// the type and default keys, so a key matching the leaf element type covers a
// multidimensional array at every level. The check must ask the element type
// rather than a subarray's, or this legal source starts failing.
TEST(ArrayLiteralElaboration, TypeKeyCoversEveryDimensionOfAMultidimArray) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[0:1][0:1] = '{int: 5};\n"
             "endmodule\n"));
}

// Syntax 10-5 lets a type key name a typedef, and §10.9.1 applies it to every
// element of that type, so it is no index key and covers the array.
TEST(ArrayPatternElaboration, TypedefTypeKeyCoversElements) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef logic [7:0] byte_t;\n"
      "module m;\n"
      "  byte_t arr[3] = '{byte_t: 8'h1};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.9.1 applies a type key to the elements whose type matches it by §6.22.1:
// a typedef of int matches int, and logic does not match logic [7:0].
TEST(ArrayPatternElaboration, TypeKeyMatchesByFullType) {
  ElabFixture f;
  ElaborateSrc(
      "typedef int myint;\n"
      "module m;\n"
      "  myint arr[3] = '{int: 5};\n"
      "  logic [7:0] b[2] = '{logic: 1'b1};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "keyed array pattern does not cover all elements",
                             3, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "keyed array pattern does not cover all elements",
                            4, "10.9.1"));
}

// §10.9.1: the braces match the dimensions, each nested pattern holding as
// many items as the dimension it stands for.
TEST(ArrayPatternElaboration, NestedPatternCountedAgainstItsDimension) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a[2][3] = '{'{1, 2}, '{3, 4, 5}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 3",
                            2, "10.9.1"));
}

// §10.9.1: a type key that matches no element of an array of structures
// descends into each and covers the element whose members it all matches.
TEST(ArrayPatternElaboration, TypeKeyCoversStructureElementsByMembers) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct { int x, y; } s_t;\n"
      "typedef struct { int x; byte y; } t_t;\n"
      "module m;\n"
      "  s_t arr[2] = '{int: 7};\n"
      "  t_t brr[2] = '{int: 7};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "keyed array pattern does not cover all elements",
                             4, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "keyed array pattern does not cover all elements",
                            5, "10.9.1"));
}

// §10.9.1 with §7.4: the braces match the array's dimensions, the packed ones
// among them, so a positional pattern initializing a packed array supplies one
// item per element of its packed dimension.
TEST(ArrayPatternElaboration, PackedVariableInitCountedAgainstPackedDimension) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] v = '{1'b1, 1'b0};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            2, "10.9.1"));
}

TEST(ArrayPatternElaboration, PackedPatternsMatchingTheirDimensionsElaborate) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [3:0] v = '{1'b1, 1'b0, 1'b1, 1'b1};\n"
             "  logic [1:0][3:0] w = '{'{1'b1, 1'b0, 1'b1, 1'b1}, 4'h2};\n"
             "  logic [7:0] r = '{8{1'b1}};\n"
             "  logic [3:0] d = '{default: 1'b0};\n"
             "  logic [3:0] k = '{logic: 1'b1};\n"
             "endmodule\n"));
}

// §10.9.1: a nested pattern stands for the next dimension in, which past the
// outer packed dimension of `w` is its inner packed one of four elements.
TEST(ArrayPatternElaboration, NestedPatternCountedAgainstInnerPackedDimension) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0][3:0] w = '{'{1'b1, 1'b0}, 4'h2};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            2, "10.9.1"));
}

// §10.9.1 with §7.4: past an array's unpacked dimensions its braces go on into
// the packed dimensions of the element type.
TEST(ArrayPatternElaboration, ElementPatternCountedAgainstPackedDimension) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a [2] = '{'{1'b1, 1'b0, 1'b1}, 4'h0};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 3 elements, but array "
                            "dimension requires 4",
                            2, "10.9.1"));
}

// §10.9.1 holds a procedure's pattern to its target as a declaration's, a
// packed array assigned by name and one a block declares alike.
TEST(ArrayPatternElaboration, ProceduralPatternCountedAgainstPackedDimension) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0][3:0] w;\n"
      "  initial w = '{4'h1, 4'h2, 4'h3};\n"
      "  initial begin\n"
      "    static logic [3:0] b = '{1'b1};\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 3 elements, but array "
                            "dimension requires 2",
                            3, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 1 elements, but array "
                            "dimension requires 4",
                            5, "10.9.1"));
}

// §6.18 with §7.4: a typedef carries its packed dimensions into the type it
// names, inside those the declaration writes on it.
TEST(ArrayPatternElaboration, TypedefPackedDimensionsCounted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  nib_t [1:0] w = '{'{1'b1, 1'b0}, 4'h0};\n"
      "  nib_t v = '{1'b1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            3, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 1 elements, but array "
                            "dimension requires 4",
                            4, "10.9.1"));
}

// §7.4: the unpacked dimensions of a typedef are outside its packed ones, so a
// pattern for `row_t` stands for its two rows, not for the four bits of each,
// whether a block declares the variable or the module declares an array of it.
TEST(ArrayPatternElaboration, TypedefUnpackedDimensionsComeBeforePackedOnes) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef logic [3:0] row_t [2];\n"
             "  row_t a [3] = '{'{4'h1, 4'h2}, '{4'h3, 4'h4}, '{4'h5, 4'h6}};\n"
             "  initial begin\n"
             "    static row_t r = '{4'h1, 4'h2};\n"
             "  end\n"
             "endmodule\n"));
}

// §7.4 with §26.3: the packed dimensions written on a type named through its
// package are counted whether or not the name resolves in the module's scope.
TEST(ArrayPatternElaboration, PackageScopedTypePackedDimensionCounted) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  typedef logic [3:0] nib_t;\n"
      "endpackage\n"
      "module m;\n"
      "  initial begin\n"
      "    static p::nib_t [1:0] w = '{4'h1, 4'h2, 4'h3};\n"
      "  end\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 3 elements, but array "
                            "dimension requires 2",
                            6, "10.9.1"));
}

// §10.9.1: a keyed pattern for a packed array covers each element by index,
// type or default as one for an unpacked array does.
TEST(ArrayPatternElaboration, KeyedPackedPatternUncoveredElementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] v = '{0: 1'b1, 1: 1'b0};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "keyed array pattern does not cover all elements",
                            2, "10.9.1"));
}

// §10.8 makes a port connection an assignment-like context, so a pattern
// connected to a packed array port supplies an item per element of its packed
// dimension. A port with an unpacked dimension as well is matched from that
// dimension first, so its four packed bits are not what a connection to it is
// counted against.
TEST(ArrayPatternElaboration, PortConnectionCountedAgainstPackedDimension) {
  ElabFixture f;
  ElaborateSrc(
      "module sc(input logic [15:0] p);\n"
      "endmodule\n"
      "module sa(input logic [3:0] p [2]);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  logic [3:0] rows [2];\n"
      "  sc u1(.p('{x, y}));\n"
      "  sc u2(.p('{16{x}}));\n"
      "  sa u3(.p(rows));\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 16",
                            8, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

// §10.8 counts a continuous assignment and a net declaration assignment among
// the assignment-like contexts, so §10.9.1 holds a pattern there to its
// target's dimensions, unpacked and packed, as it does an initializer.
TEST(ArrayPatternElaboration, ContinuousAssignmentPatternCountedAgainstTarget) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [7:0] w [0:2];\n"
      "  assign w = '{8'h1, 8'h2};\n"
      "  logic [3:0] v;\n"
      "  assign v = '{1'b1, 1'b0};\n"
      "  int a [2][3];\n"
      "  assign a = '{'{1, 2}, '{3, 4, 5}};\n"
      "  wire [3:0] n = '{1'b1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 3",
                            3, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            5, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 3",
                            7, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 1 elements, but array "
                            "dimension requires 4",
                            8, "10.9.1"));
}

TEST(ArrayPatternElaboration, ContinuousAssignmentPatternMatchingTargetOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire [7:0] w [0:2];\n"
             "  assign w = '{8'h1, 8'h2, 8'h3};\n"
             "  logic [3:0] v;\n"
             "  assign v = '{4{1'b1}};\n"
             "  wire [3:0] n = '{1'b1, 1'b0, 1'b1, 1'b0};\n"
             "endmodule\n"));
}

// §6.18 with §7.4: a port declared through a packed array typedef has the
// typedef's packed dimensions, so a pattern connected to it is counted against
// them as against dimensions the port header writes out.
TEST(ArrayPatternElaboration, PortOfPackedTypedefCountedAgainstItsDimension) {
  ElabFixture f;
  ElaborateSrc(
      "typedef logic [3:0] nib_t;\n"
      "module sub(input nib_t p);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  sub u1(.p('{x, y}));\n"
      "  sub u2(.p('{x, y, x, y}));\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            6, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

// §10.9.1: a pattern connected to a port with unpacked dimensions stands for
// those first, and a nested pattern for the packed ones inside them. A dynamic
// array port (§7.5) has no size to count against, and its connection elaborates
// past the check.
TEST(ArrayPatternElaboration, PortWithUnpackedDimensionsCountedAgainstThem) {
  ElabFixture f;
  ElaborateSrc(
      "module sub(input var int p [0:1]);\n"
      "endmodule\n"
      "module sa(input logic [3:0] q [2]);\n"
      "endmodule\n"
      "module top;\n"
      "  sub u(.p('{5, 6, 7}));\n"
      "  sa v(.q('{'{1'b1, 1'b0}, 4'h0}));\n"
      "  sd w(.d('{1, 2, 3}));\n"
      "endmodule\n"
      "module sd(input var int d []);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 3 elements, but array "
                            "dimension requires 2",
                            6, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            7, "10.9.1"));
}

// §10.9: a typed pattern takes the type its prefix names, a typedef or a type
// reference to a data type or a variable, in place of its context's, and
// §10.9.1 counts its braces against that type's dimensions, unpacked and then
// packed, as it counts an untyped pattern's against its target's.
TEST(ArrayPatternElaboration, TypedPatternCountedAgainstItsPrefixType) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  typedef int pair_t [2];\n"
      "  logic [15:0] x;\n"
      "  nib_t n;\n"
      "  int p [2];\n"
      "  assign x = type(x)'{8'd1, 8'd2};\n"
      "  initial n = nib_t'{1'b1, 1'b0};\n"
      "  initial p = pair_t'{1, 2, 3};\n"
      "  logic [23:0] y = type(logic [2:0][7:0])'{8'd1, 8'd2};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 16",
                            7, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            8, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 3 elements, but array "
                            "dimension requires 2",
                            9, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 3",
                            10, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

// §10.9.1: a typed pattern is counted wherever it is written, an operand of an
// operator and a subroutine's return value among the places, since its type
// comes from its prefix and not from an assignment it stands in.
TEST(ArrayPatternElaboration, TypedPatternCountedOutsideAssignmentLikeContext) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef logic [1:0][7:0] w_t;\n"
      "  logic [15:0] r;\n"
      "  function automatic logic [15:0] f();\n"
      "    return w_t'{8'd1, 8'd2, 8'd3};\n"
      "  endfunction\n"
      "  initial r = w_t'{8'd1, 8'd2} + w_t'{8'd3};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 3 elements, but array "
                            "dimension requires 2",
                            5, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 1 elements, but array "
                            "dimension requires 2",
                            7, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

// A typed pattern whose items match the type its prefix names elaborates, and
// `type(h)` names the declaration that is visible where it is written: the
// block's two-bit h, which hides the module's four-bit one.
TEST(ArrayPatternElaboration, TypedPatternMatchingItsPrefixTypeOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef logic [3:0] nib_t;\n"
             "  typedef int pair_t [2];\n"
             "  logic [1:0][7:0] x;\n"
             "  nib_t n;\n"
             "  int p [2];\n"
             "  logic [3:0] h;\n"
             "  parameter logic [1:0] P = 2'b01;\n"
             "  assign x = type(x)'{8'd1, 8'd2};\n"
             "  initial h = type(P)'{1'b1, 1'b0};\n"
             "  initial n = nib_t'{4{1'b1}};\n"
             "  initial p = pair_t'{1, 2};\n"
             "  initial begin\n"
             "    logic [1:0] h;\n"
             "    h = type(h)'{1'b1, 1'b0};\n"
             "  end\n"
             "endmodule\n"));
}

// §26.3 makes `p::T` the typedef T of package p, so a pattern it prefixes is
// counted against that typedef's dimensions, packed or, for an array typedef,
// unpacked (§10.9, §10.9.1).
TEST(ArrayPatternElaboration, TypedPatternWithPackageScopedPrefixCounted) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  typedef logic [3:0] T;\n"
      "  typedef int A [3];\n"
      "endpackage\n"
      "module m;\n"
      "  logic [3:0] y;\n"
      "  int a [3];\n"
      "  initial y = p::T'{1'b1, 1'b0};\n"
      "  initial a = p::A'{1, 2};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            8, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 3",
                            9, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

// The `p` before `::` names the package, so a module variable that shares its
// name has no part in the count: the pattern matches the package's two-bit T.
TEST(ArrayPatternElaboration, PackageScopedPrefixIsNoVariableOfThatName) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  typedef logic [1:0] T;\n"
             "endpackage\n"
             "module m;\n"
             "  logic [3:0] p;\n"
             "  logic [1:0] y;\n"
             "  initial y = p::T'{1'b1, 1'b0};\n"
             "endmodule\n"));
}

// §6.18: a typedef renaming an unpacked array typedef names that array, at any
// distance along the chain, so a pattern it prefixes is counted against the
// array's dimensions.
TEST(ArrayPatternElaboration, TypedPatternThroughTypedefChainCounted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int a_t [3];\n"
      "  typedef a_t b_t;\n"
      "  typedef b_t c_t;\n"
      "  int v [3];\n"
      "  initial v = b_t'{1, 2};\n"
      "  initial v = c_t'{1, 2, 3, 4};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 3",
                            6, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 4 elements, but array "
                            "dimension requires 3",
                            7, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

// §6.23 with §6.21: `type(x)` names the declaration visible where it is
// written, a block's variable or a subroutine's formal hiding the module's,
// and the pattern it prefixes is counted against that declaration's type.
TEST(ArrayPatternElaboration, TypeReferenceToBlockOrFormalCounted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] x;\n"
      "  initial begin\n"
      "    logic [3:0] x;\n"
      "    x = type(x)'{1'b1, 1'b0};\n"
      "  end\n"
      "  function automatic logic [3:0] f(input logic [3:0] a);\n"
      "    return type(a)'{1'b1, 1'b0, 1'b1};\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            5, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 3 elements, but array "
                            "dimension requires 4",
                            8, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

// Each prefix resolved as above elaborates when the items match its type.
TEST(ArrayPatternElaboration, ResolvedPrefixTypesMatchingOk) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  typedef logic [3:0] T;\n"
             "  typedef int A [3];\n"
             "endpackage\n"
             "module m;\n"
             "  typedef int a_t [3];\n"
             "  typedef a_t b_t;\n"
             "  logic [3:0] y;\n"
             "  int v [3];\n"
             "  initial y = p::T'{1'b1, 1'b0, 1'b1, 1'b0};\n"
             "  initial v = p::A'{1, 2, 3};\n"
             "  initial v = b_t'{1, 2, 3};\n"
             "  function automatic logic [3:0] f(input logic [3:0] a);\n"
             "    return type(a)'{4{1'b1}};\n"
             "  endfunction\n"
             "endmodule\n"));
}

// §6.23: `type(a_t)` stands for the type a_t names, and §7.4.4 keeps an array
// typedef's unpacked dimensions with it, so a pattern the reference prefixes
// is counted against them, a package's typedef `type(p::A)` among them.
TEST(ArrayPatternElaboration, TypeReferenceToArrayTypedefCounted) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  typedef int A [3];\n"
      "endpackage\n"
      "module m;\n"
      "  typedef int a_t [3];\n"
      "  int v [3];\n"
      "  initial v = type(a_t)'{1, 2};\n"
      "  initial v = type(p::A)'{1, 2, 3, 4};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 3",
                            7, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 4 elements, but array "
                            "dimension requires 3",
                            8, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

// A type reference to a typedef name written under packed dimensions of its own
// stands for an array of that typedef, whose dimensions come before the
// typedef's; one to a class's typedef stands for that typedef.
TEST(ArrayPatternElaboration, TypeReferenceToTypedefMatchingOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  typedef logic [3:0] T;\n"
             "endclass\n"
             "module m;\n"
             "  typedef logic [3:0] nib_t;\n"
             "  typedef int a_t [3];\n"
             "  int v [3];\n"
             "  logic [1:0][3:0] w;\n"
             "  logic [3:0] y;\n"
             "  initial v = type(a_t)'{1, 2, 3};\n"
             "  initial w = type(nib_t [1:0])'{4'h1, 4'h2};\n"
             "  initial y = type(C::T)'{4{1'b1}};\n"
             "endmodule\n"));
}

}  // namespace
