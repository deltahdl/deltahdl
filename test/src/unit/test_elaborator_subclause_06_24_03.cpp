#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §6.24.3: a bit-stream cast that converts a packed value into a packed
// aggregate of the same total width is legal.
TEST(BitStreamCastElaboration, IntToPackedStructOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  initial p = pair_t'(16'hCAFE);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.24.3: a fixed-size unpacked array whose total width matches the
// destination integral type elaborates without error.
TEST(BitStreamCastElaboration, UnpackedArrayMatchingSizeOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte arr [4];\n"
      "  int result;\n"
      "  initial result = int'(arr);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.24.3: an associative array type shall be illegal as a destination type
// for a bit-stream cast.
TEST(BitStreamCastElaboration, AssociativeArrayDestRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef byte amap_t [string];\n"
      "  byte src;\n"
      "  amap_t dst;\n"
      "  initial dst = amap_t'(src);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array type 'amap_t' is illegal as a "
                            "bit-stream cast destination",
                            5, "6.24.3"));
}

// §6.24.3: a wildcard-indexed associative array is also rejected as a
// destination type.
TEST(BitStreamCastElaboration, WildcardAssocDestRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef byte wmap_t [*];\n"
      "  byte src;\n"
      "  wmap_t dst;\n"
      "  initial dst = wmap_t'(src);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array type 'wmap_t' is illegal as a "
                            "bit-stream cast destination",
                            5, "6.24.3"));
}

// §6.24.3: a class-handle-keyed associative array is also rejected as a
// destination type. Exercises the user-defined-key branch of the typedef
// tracker, which is independent of the built-in-key branch.
TEST(BitStreamCastElaboration, ClassKeyedAssocDestRejected) {
  ElabFixture f;
  ElaborateSrc(
      "class Key;\n"
      "endclass\n"
      "module m;\n"
      "  typedef byte kmap_t [Key];\n"
      "  byte src;\n"
      "  kmap_t dst;\n"
      "  initial dst = kmap_t'(src);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array type 'kmap_t' is illegal as a "
                            "bit-stream cast destination",
                            7, "6.24.3"));
}

// §6.24.3: alongside the associative-array prohibition, a class type is also
// illegal as a bit-stream cast destination when the source is not itself a
// class handle.
//
// The report names §8.4 and not §6.24.3, because
// `Elaborator::CheckBitStreamCastExpr` exempts a destination that names a
// class and the rejection comes from `CheckClassHandleCast` in
// src/elaborator/elaborator_validate_class_handles.cpp instead.
TEST(BitStreamCastElaboration, ClassDestFromNonClassRejected) {
  ElabFixture f;
  ElaborateSrc(
      "class Container;\n"
      "endclass\n"
      "module m;\n"
      "  int src;\n"
      "  Container c;\n"
      "  initial c = Container'(src);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot cast non-class value to a class type", 6,
                            "8.4"));
}

// §6.24.3: a class handle whose class has a local member is illegal as a
// bit-stream cast source.
TEST(BitStreamCastElaboration, ClassWithLocalSourceRejected) {
  ElabFixture f;
  ElaborateSrc(
      "class Hidden;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Hidden h;\n"
      "  int v;\n"
      "  initial v = int'(h);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class handle 'h' is illegal as a bit-stream cast "
                            "source: its class has local or protected members",
                            7, "6.24.3"));
}

// §6.24.3: a class handle whose class has a protected member is also illegal
// as a bit-stream cast source.
TEST(BitStreamCastElaboration, ClassWithProtectedSourceRejected) {
  ElabFixture f;
  ElaborateSrc(
      "class Hidden;\n"
      "  protected int hidden;\n"
      "endclass\n"
      "module m;\n"
      "  Hidden h;\n"
      "  int v;\n"
      "  initial v = int'(h);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class handle 'h' is illegal as a bit-stream cast "
                            "source: its class has local or protected members",
                            7, "6.24.3"));
}

// §6.24.3: when source and destination are both fixed-size types of different
// sizes and the operand is an unpacked array, a compile-time error must be
// raised.
TEST(BitStreamCastElaboration, FixedSizeMismatchUnpackedRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  initial result = int'(arr);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            4, "6.24.3"));
}

// §6.24.3: a bit-stream cast to a packed struct of the wrong total width when
// the operand is an unpacked array is rejected at compile time.
TEST(BitStreamCastElaboration, UnpackedToStructWrongWidthRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } "
      "pair_t;\n"
      "  byte arr [3];\n"
      "  pair_t p;\n"
      "  initial p = pair_t'(arr);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 16 bits) with an "
                            "unpacked operand is illegal",
                            5, "6.24.3"));
}

// §6.24.3: a bit-stream cast in a continuous assignment is validated the same
// way an initial-block cast is.
TEST(BitStreamCastElaboration, ContAssignFixedSizeMismatchRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  assign result = int'(arr);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            4, "6.24.3"));
}

// §6.24.3: the fixed-size mismatch rule also fires when the destination is an
// unpacked-array typedef and the source is a fixed-width packed literal of a
// different total width.
TEST(BitStreamCastElaboration, FixedSizeMismatchUnpackedDestRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef byte arr4_t [4];\n"
      "  arr4_t a;\n"
      "  initial a = arr4_t'(16'hABCD);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (16 bits to 32 bits) with an "
                            "unpacked destination is illegal",
                            4, "6.24.3"));
}

// §6.24.3: when the source's packed width matches the typedef destination's
// total unpacked width, the cast elaborates without error.
TEST(BitStreamCastElaboration, FixedSizeMatchUnpackedDestOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef byte arr4_t [4];\n"
      "  arr4_t a;\n"
      "  initial a = arr4_t'(32'hDEADBEEF);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.24.3: a bit-stream cast between fixed-size types of different sizes with
// an unpacked destination is illegal. §11.4.14 makes the source stream four
// bits wide, the width of its one operand, against the sixteen bits of
// arr2_t, and the report names both.
TEST(BitStreamCastElaboration,
     StreamSourceNarrowerThanUnpackedDestinationRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef byte arr2_t [2];\n"
      "  arr2_t a;\n"
      "  initial a = arr2_t'({>> {4'b1100}});\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (4 bits to 16 bits) with an "
                            "unpacked destination is illegal",
                            4, "6.24.3"));
}

// §6.24.3: the same cast is legal when the two sizes agree. §11.4.14 sums the
// stream's two eight-bit operands to the sixteen bits of arr2_t, so nothing is
// reported. A check that rejected every streaming source would satisfy the
// case above and fail here.
TEST(BitStreamCastElaboration, StreamSourceMatchingUnpackedDestinationWidthOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef byte arr2_t [2];\n"
      "  arr2_t a;\n"
      "  initial a = arr2_t'({>> {8'hAB, 8'hCD}});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.24.3 makes a bit-stream cast between fixed-size types of different sizes
// illegal when either is unpacked, and names no statement the cast is allowed
// to stand in, so every position a statement holds a statement in is one the
// report reaches. ElaboratorOperationRules::WalkStmtsForBitStreamCast in
// src/elaborator/elaborator_validate_operations_streaming.cpp had written out
// six of the thirteen child-statement links Stmt declares and now takes the
// list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. The seven cases below stand in
// the seven positions it was missing, each of which elaborated clean beforehand
// with the illegal cast unreported. Each casts the same 24-bit unpacked array
// to a 32-bit int that FixedSizeMismatchUnpackedRejected above establishes as
// illegal in an initial-block statement.

// A.6.3 gives `par_block ::= fork [ : block_identifier ]
// { block_item_declaration } { statement_or_null } join_keyword ...`, so a fork
// holds statements the way a begin-end block does. The parser keeps them in
// Stmt::fork_stmts rather than in Stmt::stmts.
TEST(BitStreamCastElaboration, FixedSizeMismatchInAForkStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  initial fork\n"
      "    result = int'(arr);\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            5, "6.24.3"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...`, so
// the loop header holds assignments of its own, kept in Stmt::for_inits.
TEST(BitStreamCastElaboration, FixedSizeMismatchInAForInitializerRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  int i;\n"
      "  initial\n"
      "    for (result = int'(arr); i < 1; i = i + 1)\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            6, "6.24.3"));
}

// A.6.8's `for_step_assignment ::= operator_assignment | ...` is the same rule
// at the other end of the loop header, kept in Stmt::for_steps. The initializer
// here assigns a constant, so the report can only be about the step.
TEST(BitStreamCastElaboration, FixedSizeMismatchInAForStepRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; result = int'(arr))\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            6, "6.24.3"));
}

// A.6.10 gives `simple_immediate_assert_statement ::= assert ( expression )
// action_block` and §16.3 gives `action_block ::= statement_or_null |
// [ statement ] else statement_or_null`, so the pass arm of an immediate
// assertion holds an ordinary statement, kept in Stmt::assert_pass_stmt.
TEST(BitStreamCastElaboration,
     FixedSizeMismatchInAnAssertionPassStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  logic ok;\n"
      "  initial assert (ok) result = int'(arr);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            5, "6.24.3"));
}

// The else arm of the same production, kept in Stmt::assert_fail_stmt, a link
// the pass-arm case above does not reach.
TEST(BitStreamCastElaboration,
     FixedSizeMismatchInAnAssertionFailStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  logic armed;\n"
      "  initial assert (armed) else result = int'(arr);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            5, "6.24.3"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. §6.24.3
// judges the cast rather than whether it runs, so the report stands whether the
// weighted draw would select the item or not.
TEST(BitStreamCastElaboration, FixedSizeMismatchInARandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  initial randcase 1: result = int'(arr); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            4, "6.24.3"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(BitStreamCastElaboration,
     FixedSizeMismatchInARandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { result = int'(arr); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            6, "6.24.3"));
}

}  // namespace
