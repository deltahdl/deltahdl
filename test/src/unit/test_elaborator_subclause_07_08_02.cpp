#include <gtest/gtest.h>

#include <cstdint>

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

// §7.8.2: a string index shall be a string, whatever form the index takes: an
// arithmetic operator gives an integral or real value and any other operator
// an integral one, while a string method may give a string.
TEST(StringIndexAssocArrayElaboration, NonStringIndexExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 1;\n"
      "  int s [string];\n"
      "  int i;\n"
      "  real r;\n"
      "  string t;\n"
      "  int a[2];\n"
      "  initial begin\n"
      "    s[i + 1] = 1;\n"
      "    s[r * 2] = 1;\n"
      "    s[i == 1] = 1;\n"
      "    s[P + 1] = 1;\n"
      "    s[t.substr(0, 1)] = 1;\n"
      "    s[a[0]] = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line = 9; line <= 12; ++line) {
    EXPECT_TRUE(ReportedError(diags,
                              "string-indexed associative array 's' shall be "
                              "indexed by a string or string literal",
                              line, "7.8.2"));
  }
  for (const auto& d : diags) EXPECT_NE(d.loc.line, 13u) << d.message;
}

// §7.8.2: a string index shall be a string, and a select, a cast, a function
// call or a concatenation gives the type its declaration states: an int
// array's element, a string's character, a net's bit, a real array's element,
// a cast to int, an int negated, an integral concatenation and a class array's
// element are no string; a string array's element, a function returning a
// string, a cast to string and a concatenation holding a string are.
TEST(StringIndexAssocArrayElaboration, NonStringSelectCastAndCallRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class K; endclass\n"
      "  int s [string];\n"
      "  string t;\n"
      "  string sa [2];\n"
      "  int a [2];\n"
      "  real ra [2];\n"
      "  K ka [2];\n"
      "  wire [3:0] wv;\n"
      "  function string g(); return \"x\"; endfunction\n"
      "  initial begin\n"
      "    s[a[0]] = 1;\n"
      "    s[t[0]] = 1;\n"
      "    s[wv[1]] = 1;\n"
      "    s[ra[0]] = 1;\n"
      "    s[int'(3)] = 1;\n"
      "    s[-a[1]] = 1;\n"
      "    s[{a[0], a[1]}] = 1;\n"
      "    s[ka[0]] = 1;\n"
      "    s[sa[1]] = 1;\n"
      "    s[g()] = 1;\n"
      "    s[string'(a[0])] = 1;\n"
      "    s[{t, \"x\"}] = 1;\n"
      "    s[{a[0], \"x\", a[1]}] = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const char* const kReport =
      "string-indexed associative array 's' shall be indexed by a string or "
      "string literal";
  for (uint32_t line = 12; line <= 19; ++line) {
    EXPECT_TRUE(ReportedError(diags, kReport, line, "7.8.2"));
  }
  for (uint32_t line = 20; line <= 24; ++line) {
    EXPECT_FALSE(ReportedError(diags, kReport, line, "7.8.2"));
  }
}

}  // namespace
