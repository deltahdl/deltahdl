#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(StringIndexAssocArrayElaboration, AssocDimElaboratesStringIndex) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa [string]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_assoc);
  EXPECT_TRUE(mod->variables[0].is_string_index);
}

TEST(StringIndexAssocArrayElaboration, NotWildcardIndex) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa [string]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_FALSE(v.is_wildcard_index);
}

TEST(StringIndexAssocArrayElaboration, VectorElementType) {
  ElabFixture f;
  auto* design = Elaborate("module m; bit [7:0] aa [string]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_TRUE(v.is_assoc);
  EXPECT_TRUE(v.is_string_index);
  EXPECT_EQ(v.width, 8u);
}

// §7.8.2: a string literal index of any length is a valid index.
TEST(StringIndexAssocArrayElaboration, StringLiteralIndexNoError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  initial aa[\"key\"] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.8.2: a string-typed variable is a valid index.
TEST(StringIndexAssocArrayElaboration, StringVariableIndexNoError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  string s;\n"
      "  initial aa[s] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.8.2: indexing with a non-string literal is a different type and shall be
// reported as a type check error.
TEST(StringIndexAssocArrayElaboration, IntegerLiteralIndexIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  initial aa[7] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string-indexed associative array 'aa' shall be "
                            "indexed by a string or string literal",
                            3, "7.8.2"));
}

// §7.8.2: indexing with a variable of a non-string type is a type check error.
TEST(StringIndexAssocArrayElaboration, IntegerVariableIndexIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int i;\n"
      "  initial aa[i] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string-indexed associative array 'aa' shall be "
                            "indexed by a string or string literal",
                            4, "7.8.2"));
}

// §7.8.2: string literals of any length are valid indices, so the
// zero-length empty string literal is accepted without a type check error.
TEST(StringIndexAssocArrayElaboration, EmptyStringLiteralIndexNoError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  initial aa[\"\"] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.8.2: the illegal-index rule applies wherever the array is indexed, not
// only when it is the assignment target. A non-string index in a read (an
// index used as a source operand) is a type check error just the same.
TEST(StringIndexAssocArrayElaboration, IntegerLiteralIndexInReadIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int x;\n"
      "  initial x = aa[7];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string-indexed associative array 'aa' shall be "
                            "indexed by a string or string literal",
                            4, "7.8.2"));
}

// The seven cases below stand in the seven statement positions
// WalkStmtsForStringIndexSelect in
// src/elaborator/elaborator_validate_class_array_index.cpp reached only once it
// took its list of nested statements from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. Each writes the integer index
// IntegerLiteralIndexIsError above writes in a plain initial statement, and
// §7.8.2 rules on it the same way wherever it stands. Each elaborated clean
// beforehand.

// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword [ :
// block_identifier ]`, so a fork arm is a statement position like any other.
TEST(StringIndexAssocArrayElaboration, IntegerIndexInAForkArmIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int x;\n"
      "  initial begin\n"
      "    fork\n"
      "      x = aa[7];\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string-indexed associative array 'aa' shall be "
                            "indexed by a string or string literal",
                            6, "7.8.2"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm.
// This case covers the pass arm and the one below it the else arm.
TEST(StringIndexAssocArrayElaboration,
     IntegerIndexInAnAssertionPassStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int x;\n"
      "  logic ok;\n"
      "  initial assert (ok) x = aa[7];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string-indexed associative array 'aa' shall be "
                            "indexed by a string or string literal",
                            5, "7.8.2"));
}

TEST(StringIndexAssocArrayElaboration,
     IntegerIndexInAnAssertionFailStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int x;\n"
      "  logic ok;\n"
      "  initial assert (ok) else x = aa[7];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string-indexed associative array 'aa' shall be "
                            "indexed by a string or string literal",
                            5, "7.8.2"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`. The type
// check is a static one, so it holds whether the weighted draw would select
// the item or not.
TEST(StringIndexAssocArrayElaboration, IntegerIndexInARandcaseItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int x;\n"
      "  initial randcase 1: x = aa[7]; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string-indexed associative array 'aa' shall be "
                            "indexed by a string or string literal",
                            4, "7.8.2"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements.
TEST(StringIndexAssocArrayElaboration,
     IntegerIndexInARandsequenceCodeBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = aa[7]; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string-indexed associative array 'aa' shall be "
                            "indexed by a string or string literal",
                            6, "7.8.2"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// `for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call`, so an assignment stands at each of the two
// positions: this case writes one at the initialization and the case below it
// writes one at the step.
TEST(StringIndexAssocArrayElaboration,
     IntegerIndexInAForLoopInitializationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int x;\n"
      "  int i;\n"
      "  initial for (x = aa[7]; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string-indexed associative array 'aa' shall be "
                            "indexed by a string or string literal",
                            5, "7.8.2"));
}

TEST(StringIndexAssocArrayElaboration, IntegerIndexInAForLoopStepIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int x;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; x = aa[7]) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string-indexed associative array 'aa' shall be "
                            "indexed by a string or string literal",
                            5, "7.8.2"));
}

}  // namespace
