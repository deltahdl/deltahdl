#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IntegralIndexAssocArrayElaboration, AssocArrayByteIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[byte];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 8u);
}

TEST(IntegralIndexAssocArrayElaboration, AssocArrayIntIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 32u);
}

TEST(IntegralIndexAssocArrayElaboration, AssocArrayShortintIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[shortint];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 16u);
}

TEST(IntegralIndexAssocArrayElaboration, AssocArrayLongintIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[longint];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 64u);
}

TEST(IntegralIndexAssocArrayElaboration, AssocArrayIntegerIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[integer];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 32u);
}

TEST(IntegralIndexAssocArrayElaboration, NotStringIndex) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_FALSE(v.is_string_index);
  EXPECT_FALSE(v.is_wildcard_index);
}

// §7.8.4: ordering and casting follow the signedness of the index type. The
// built-in integral index types are signed.
TEST(IntegralIndexAssocArrayElaboration, BuiltinIntIndexIsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_TRUE(v.is_assoc);
  EXPECT_TRUE(v.is_index_signed);
}

// §7.8.4: a typedef'd unsigned index type (bit without `signed`) orders
// unsigned, so its index is recorded as unsigned.
TEST(IntegralIndexAssocArrayElaboration, UnsignedTypedefIndex) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef bit [4:1] UNibble;\n"
      "  int map[UNibble];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_TRUE(v.is_assoc);
  EXPECT_EQ(v.assoc_index_width, 4u);
  EXPECT_FALSE(v.is_index_signed);
}

// §7.8.4: a typedef'd signed index type orders signed.
TEST(IntegralIndexAssocArrayElaboration, SignedTypedefIndex) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef bit signed [4:1] SNibble;\n"
      "  int map[SNibble];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_TRUE(v.is_assoc);
  EXPECT_EQ(v.assoc_index_width, 4u);
  EXPECT_TRUE(v.is_index_signed);
}

// §7.8.4: an implicit cast from a real expression to an integral index type is
// illegal. (A procedural index select; the continuous-assign real-select check
// does not cover procedural bodies.)
TEST(IntegralIndexAssocArrayElaboration, RealIndexExprIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  initial map[r] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            4, "7.8.4"));
}

// §7.8.4: the prohibition on an implicit cast covers shortreal as well as real.
TEST(IntegralIndexAssocArrayElaboration, ShortrealIndexExprIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  shortreal s;\n"
      "  initial map[s] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            4, "7.8.4"));
}

// §7.8.4: an integral index expression is legal and casts cleanly.
TEST(IntegralIndexAssocArrayElaboration, IntegerIndexExprLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  initial map[5] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §7.8.4: the illegal-implicit-cast rule covers a real *literal* index, not
// only a real-typed variable — a distinct input form that reaches the check by
// literal kind rather than by variable type.
TEST(IntegralIndexAssocArrayElaboration, RealLiteralIndexIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  initial map[3.7] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            3, "7.8.4"));
}

// §7.8.4: the prohibition applies wherever the array is indexed, including a
// read (an index select on the right-hand side), not just a write target.
TEST(IntegralIndexAssocArrayElaboration, RealIndexInReadPositionIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  int x;\n"
      "  initial x = map[r];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            5, "7.8.4"));
}

// §7.8.4: only the *implicit* cast from real is illegal. An explicit cast of a
// real value to an integral type (§6.24.1) yields an integral index and is
// legal, so wrapping the real operand in int'(...) defeats the prohibition.
TEST(IntegralIndexAssocArrayElaboration, ExplicitRealCastIndexLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  initial map[int'(r)] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// A.2.2.1 gives `data_type ::= integer_vector_type [ signing ] {
// packed_dimension } | ...` and §7.8 makes an associative array's index_type a
// data type, so `bit [3:0]` is a legal index type written inline, without a
// typedef naming it. §7.8.4 keys an entry off the index cast to the declared
// index width, so the packed dimension has to reach that width: the inline
// form must record the same width 4 and unsigned signedness the typedef'd
// `bit [4:1]` form above records, rather than being parsed and dropped.
TEST(IntegralIndexAssocArrayElaboration, InlinePackedDimensionIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int aa[bit[3:0]];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 4u);
  EXPECT_FALSE(vars[0].is_index_signed);
}

// The seven cases below stand in the seven statement positions
// WalkStmtsForIntegralIndexSelect in
// src/elaborator/elaborator_validate_class_array_index.cpp reached only once it
// took its list of nested statements from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. Each writes the real index
// RealIndexExprIllegal above writes in a plain initial statement, and §7.8.4
// rules on it the same way wherever it stands. Each elaborated clean
// beforehand. The walk emits the one report of Subclause("7.8.4"); the §7.8.5
// rule on a real index *type* is reported at the declaration instead, so it
// has no statement position to cover.

// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword [ :
// block_identifier ]`, so a fork arm is a statement position like any other.
TEST(IntegralIndexAssocArrayElaboration, RealIndexInAForkArmIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  int x;\n"
      "  initial begin\n"
      "    fork\n"
      "      x = map[r];\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            7, "7.8.4"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm.
// This case covers the pass arm and the one below it the else arm.
TEST(IntegralIndexAssocArrayElaboration,
     RealIndexInAnAssertionPassStatementIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  int x;\n"
      "  logic ok;\n"
      "  initial assert (ok) x = map[r];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            6, "7.8.4"));
}

TEST(IntegralIndexAssocArrayElaboration,
     RealIndexInAnAssertionFailStatementIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  int x;\n"
      "  logic ok;\n"
      "  initial assert (ok) else x = map[r];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            6, "7.8.4"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`. The rule is
// a static one, so it holds whether the weighted draw would select the item or
// not.
TEST(IntegralIndexAssocArrayElaboration, RealIndexInARandcaseItemIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  int x;\n"
      "  initial randcase 1: x = map[r]; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            5, "7.8.4"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements.
TEST(IntegralIndexAssocArrayElaboration,
     RealIndexInARandsequenceCodeBlockIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  int x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = map[r]; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            7, "7.8.4"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// `for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call`, so an assignment stands at each of the two
// positions: this case writes one at the initialization and the case below it
// writes one at the step.
TEST(IntegralIndexAssocArrayElaboration,
     RealIndexInAForLoopInitializationIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  int x;\n"
      "  int i;\n"
      "  initial for (x = map[r]; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            6, "7.8.4"));
}

TEST(IntegralIndexAssocArrayElaboration, RealIndexInAForLoopStepIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "  real r;\n"
      "  int x;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; x = map[r]) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal index is not allowed on "
                            "integral-indexed associative array 'map'",
                            6, "7.8.4"));
}

}  // namespace
