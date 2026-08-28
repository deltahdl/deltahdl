
#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "helpers_stmt_exec.h"
#include "simulator/compiled_sim.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ArrayAddressingElaboration, WriteAndReadArrayElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  initial begin mem[0] = 8'h00; mem[2] = 8'hAB; end\n"
      "endmodule\n",
      f, "mem[2]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(ArrayAddressingElaboration, MultiDimArrayElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] mem [0:3][0:3];\n"
             "  int result;\n"
             "  initial result = mem[1][2];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, MemoryIndirectionElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] mem [0:7];\n"
             "  int result;\n"
             "  initial result = mem[mem[3]];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, BitSelectAfterArrayElementElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] arr [0:3];\n"
             "  logic result;\n"
             "  initial result = arr[2][5];\n"
             "endmodule\n"));
}

// §11.5.2 — a bit-select or part-select of an array element requires an address
// for every dimension first. Addressing all dimensions, then part-selecting the
// selected word, is legal.
TEST(ArrayAddressingElaboration, PartSelectAfterAllDimensionsAddressed) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] twod [0:3][0:3];\n"
             "  logic [3:0] result;\n"
             "  initial result = twod[1][2][3:0];\n"
             "endmodule\n"));
}

// §11.5.2 — the positive boundary for a three-dimensional array: once all three
// dimensions are addressed the selected item is a vector, so a part-select of
// it is legal. This is the accepting twin of the rejections below.
TEST(ArrayAddressingElaboration, PartSelectAfterAllThreeDimensionsAddressed) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] threed [0:3][0:3][0:7];\n"
             "  logic [3:0] result;\n"
             "  initial result = threed[2][1][0][3:0];\n"
             "endmodule\n"));
}

// The cases below all leave one dimension unaddressed, so §11.5.2's rule about
// reaching into a word does not reach them. That rule is written about
// bit-selects and part-selects of array elements — "the desired word shall
// first be selected by supplying an address for each dimension" — and §7.4.5
// defines a part-select as a selection of contiguous bits of a packed array.
// A trailing range over a dimension carrying no address selects contiguous
// *elements* instead, which §7.4.5 calls a slice and permits: "Slices of an
// array can only apply to one dimension, but other dimensions can have single
// index values in an expression." What decides these cases is therefore not the
// unaddressed dimension but the direction the range is written in.

// §11.5.1 requires the first index of a range to "address a more significant
// bit than the second expression", and §11.5.2 sends an array's ranges to that
// same rule. The third dimension is declared [0:7] and counts upward, so its
// more significant element is the one with the smaller index and [0:3] names
// its first four elements in order.
TEST(ArrayAddressingElaboration, AscendingSliceOfAnAscendingDimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] threed [0:3][0:3][0:7];\n"
             "  logic [31:0] result;\n"
             "  initial result = threed[2][1][0:3];\n"
             "endmodule\n"));
}

// The same declaration and the same four elements, written backwards. This is
// the shape §11.5.2 marks illegal, and the direction is what makes it so.
TEST(ArrayAddressingElaboration,
     DescendingSliceOfAnAscendingDimensionIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [7:0] threed [0:3][0:3][0:7];\n"
      "  logic [31:0] result;\n"
      "  initial result = threed[2][1][3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "slice's first index must address a more significant element", 4,
      "11.5.2"));
}

// The twin declaration, whose third dimension is written [7:0] and counts
// downward. The range rejected just above is the one written in order here, and
// the range accepted just above is the one written backwards. Without this pair
// a check that rejected every descending range would pass both tests above,
// because every other array in this file counts upward.
TEST(ArrayAddressingElaboration, DescendingSliceOfADescendingDimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] dthreed [0:3][0:3][7:0];\n"
             "  logic [31:0] result;\n"
             "  initial result = dthreed[2][1][3:0];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration,
     AscendingSliceOfADescendingDimensionIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [7:0] dthreed [0:3][0:3][7:0];\n"
      "  logic [31:0] result;\n"
      "  initial result = dthreed[2][1][0:3];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "slice's first index must address a more significant element", 4,
      "11.5.2"));
}

// §11.5.1 ties an indexed range to the declared direction whichever way that
// direction runs: on the upward-counting `logic [0:31] b_vect` it gives
// b_vect[0 +: 8] == b_vect[0:7] and b_vect[15 -: 8] == b_vect[8:15]. An indexed
// slice therefore cannot be written backwards, and both forms name four
// elements of the upward-counting [0:7] dimension legally.
TEST(ArrayAddressingElaboration, AscendingIndexedSliceOfADimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] threed [0:3][0:3][0:7];\n"
             "  logic [31:0] result;\n"
             "  initial result = threed[2][1][0 +: 4];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, DescendingIndexedSliceOfADimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] threed [0:3][0:3][0:7];\n"
             "  logic [31:0] result;\n"
             "  initial result = threed[2][1][3 -: 4];\n"
             "endmodule\n"));
}

// §11.5.2's own illegal example, on the declaration the clause writes it
// against: `wire threed_array[0:255][0:255][0:7]` is an array of
// 256-by-256-by-8 single-bit elements, with no packed dimension at all, and
// threed_array[14][1][3:0] is marked "// Illegal". Its third dimension counts
// upward, so the range runs backwards over the elements it slices.
TEST(ArrayAddressingElaboration,
     DescendingSliceOfAnAscendingBitDimensionIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  wire threed_array [0:255][0:255][0:7];\n"
      "  wire [3:0] result;\n"
      "  assign result = threed_array[14][1][3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "slice's first index must address a more significant element", 4,
      "11.5.2"));
}

// The accepting twin of the case above, on one declaration with the slice's
// direction the only difference. Without it a check refusing every slice of a
// net array would pass the rejection above, since before this a net array could
// not be indexed at all.
TEST(ArrayAddressingElaboration,
     AscendingSliceOfAnAscendingNetDimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire threed_array [0:255][0:255][0:7];\n"
             "  wire [3:0] result;\n"
             "  assign result = threed_array[14][1][0:3];\n"
             "endmodule\n"));
}

// §7.4.2: "Unpacked arrays can be made of any data type", and "Elements of net
// arrays can be used in the same fashion as a scalar or vector net" — the
// clause names connecting module instance ports inside loop generate constructs
// as what net arrays are for. Indexing one was refused outright, because
// Elaborator::ElaborateNetDecl asked only whether the net carried a packed
// dimension and so made `wire w [3:0]` a scalar. The range is written [3:0]
// rather than [0:3] because on a range starting at zero an index and a storage
// offset are the same number, so code confusing the two answers correctly.
TEST(ArrayAddressingElaboration, IndexingAnUnpackedNetArrayIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire w [3:0];\n"
             "  wire x;\n"
             "  assign x = w[1];\n"
             "endmodule\n"));
}

// §11.5.1: "A bit-select or part-select of a scalar ... shall be illegal." A
// net with no dimension at all is still a scalar, which is what stops the fix
// above from emptying scalar_var_names_ for every net. No test named a scalar
// net before, so the rule was pinned for variables alone.
TEST(ArrayAddressingElaboration, IndexingAScalarNetIsStillIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  wire s;\n"
      "  wire x;\n"
      "  assign x = s[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            4, "11.5.1"));
}

// §7.6's array assignment comparison reads var_array_info_, which holds
// variables alone, so a net array assigned from a variable array is judged
// exactly as it was before this change. This is the case that went red when the
// net's dimensions were recorded in that map instead of net_array_info_:
// VarArrayInfo::elem_type is the net kind for a wire and kLogic for the
// variable, and §6.7.1 makes a net's default data type logic, so the mismatch
// it reported was not one.
TEST(ArrayAddressingElaboration, AssigningAVariableArrayToANetArrayIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] v[4];\n"
             "  wire [7:0] w[4];\n"
             "  assign w = v;\n"
             "endmodule\n"));
}

// §7.4.2: a dimension declared by a size alone is the range [0:size-1], which
// counts upward, so a slice of it is written with the lower index first. This
// is the form reported in #2856, and the pair pins that a size records a
// direction rather than leaving one unset — read as having no direction, both
// of these would come out the same way.
TEST(ArrayAddressingElaboration, AscendingSliceOfASizedDimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  initial r = A[1][0:1];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, DescendingSliceOfASizedDimensionIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int A[2][3];\n"
      "  logic [63:0] r;\n"
      "  initial r = A[1][1:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "slice's first index must address a more significant element", 4,
      "11.5.2"));
}

// The four cases below address every dimension, so the trailing range is a
// part-select of the word the addressing selected rather than a slice. §11.5.2
// sends it to §11.5.1 -- "Once selected, bit-selects and part-selects shall be
// addressed in the same manner as net and variable bit-selects and
// part-selects" -- and §11.5.1 requires the first index to address a more
// significant bit than the second. Which index that is comes from the element's
// own declared range, so the same part-select is legal against one element
// declaration and illegal against the other.
//
// Every other array in this file declares its element [7:0]. On a range ending
// at zero the index of a bit and its distance from the least significant end
// are the same number, so those tests answer alike whether the declaration is
// consulted or ignored. The pair below is what tells the two apart: `arr` and
// `darr` differ only in the direction of the element, and the verdicts swap.

TEST(ArrayAddressingElaboration,
     AscendingPartSelectOfAnAscendingElementIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [0:7] arr [0:3];\n"
             "  logic [3:0] result;\n"
             "  initial result = arr[2][0:3];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration,
     DescendingPartSelectOfAnAscendingElementIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [0:7] arr [0:3];\n"
      "  logic [3:0] result;\n"
      "  initial result = arr[2][3:0];\n"
      "endmodule\n",
      f);
  // Every dimension is addressed, so §11.5.2 hands the range to §11.5.1 and the
  // report names that clause rather than this file's.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more "
                            "significant bit",
                            4, "11.5.1"));
}

TEST(ArrayAddressingElaboration,
     DescendingPartSelectOfADescendingElementIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] darr [0:3];\n"
             "  logic [3:0] result;\n"
             "  initial result = darr[2][3:0];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration,
     AscendingPartSelectOfADescendingElementIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [7:0] darr [0:3];\n"
      "  logic [3:0] result;\n"
      "  initial result = darr[2][0:3];\n"
      "endmodule\n",
      f);
  // As above: the addressing is complete, so §11.5.1 is the clause reported.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more "
                            "significant bit",
                            4, "11.5.1"));
}

// §11.5.2 sends an array's trailing range to §11.5.1's ordering rule, which
// governs the range itself and not the statement holding it. A slice written
// against the direction of the dimension it slices is illegal wherever it
// stands.
//
// ElaboratorOperationRules::WalkStmtsForArrayElementPartSelect in
// src/elaborator/elaborator_validate_operations_arrays.cpp reached six of the
// thirteen statement links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states. The seven cases here
// each put `r = A[1][1:0]` in one of the seven positions it did not read, every
// one of which elaborated clean beforehand.
//
// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword [ :
// block_identifier ]`, so a fork arm is a statement position like any other.
TEST(ArrayAddressingElaboration, ReversedSliceInAForkArmNames11_5_2) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  initial begin\n"
             "    fork\n"
             "      r = A[1][1:0];\n"
             "    join\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice's first index must address a more", 6,
                            "11.5.2"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case covers
// the pass arm and the one below it the fail arm.
TEST(ArrayAddressingElaboration,
     ReversedSliceInAnAssertionPassStatementNames11_5_2) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  logic ok;\n"
             "  initial assert (ok) r = A[1][1:0];\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice's first index must address a more", 5,
                            "11.5.2"));
}

TEST(ArrayAddressingElaboration,
     ReversedSliceInAnAssertionFailStatementNames11_5_2) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  logic ok;\n"
             "  initial assert (ok) else r = A[1][1:0];\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice's first index must address a more", 5,
                            "11.5.2"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. The rule
// is a static one, so it holds whether the weighted draw would select the item
// or not.
TEST(ArrayAddressingElaboration, ReversedSliceInARandcaseItemNames11_5_2) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  initial randcase 1: r = A[1][1:0]; endcase\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice's first index must address a more", 4,
                            "11.5.2"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions.
TEST(ArrayAddressingElaboration,
     ReversedSliceInARandsequenceCodeBlockNames11_5_2) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  initial begin\n"
             "    randsequence(main)\n"
             "      main : { r = A[1][1:0]; };\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice's first index must address a more", 6,
                            "11.5.2"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments |
// for_variable_declaration { , for_variable_declaration }` and
// `for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call`. A.6.2 gives `variable_assignment ::=
// variable_lvalue = expression` and `operator_assignment ::= variable_lvalue
// assignment_operator expression`, whose assignment_operator includes `=`, so
// an assignment stands at each of the two positions: this case writes one at
// the initialization and the case below it writes one at the step.
TEST(ArrayAddressingElaboration,
     ReversedSliceInAForLoopInitializationNames11_5_2) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  int i;\n"
             "  initial for (r = A[1][1:0]; i < 1; i = i + 1) ;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice's first index must address a more", 5,
                            "11.5.2"));
}

TEST(ArrayAddressingElaboration, ReversedSliceInAForLoopStepNames11_5_2) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  int i;\n"
             "  initial for (i = 0; i < 1; r = A[1][1:0]) ;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice's first index must address a more", 5,
                            "11.5.2"));
}

}  // namespace
