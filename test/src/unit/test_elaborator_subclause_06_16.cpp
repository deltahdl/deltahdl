#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(Elaboration, StringVarIsString) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  string s;\n"
      "  initial s = \"hello\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "s") {
      found = true;
      EXPECT_TRUE(v.is_string);
    }
  }
  EXPECT_TRUE(found) << "string variable 's' not found";
}

TEST(Elaboration, StringDefaultEmptyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  string s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, StringWithLiteralInitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  string s = \"test\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.16, Table 6-9: a string replication multiplier shall be a non-negative,
// non-x, non-z integral expression. A multiplier containing x is rejected, and
// the report is the §11.4.12.1 one that governs every replication multiplier;
// it stands at the multiplier literal.
TEST(Elaboration, StringReplicationXZMultiplierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  string s;\n"
      "  initial s = {1'bx{\"ab\"}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication multiplier shall not contain x or z",
                            3, "11.4.12.1"));
}

// §6.16: indexing a string variable selects one character of it to read or
// write. Both directions are accepted: the read and the write are the same
// selection.
TEST(Elaboration, StringVarMayBeIndexedForReadingAndWriting) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  string s = \"world\";\n"
             "  byte c;\n"
             "  initial begin\n"
             "    c = s[2];\n"
             "    s[1] = \"a\";\n"
             "  end\n"
             "endmodule\n"));
}

// The same rule reaches a variable whose type is written as a name: what
// decides whether indexing is a character selection is the type the name
// stands for, not the spelling at the declaration.
TEST(Elaboration, IndexingAVarOfTypedefedStringType) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  typedef string str_t;\n"
             "  str_t s = \"world\";\n"
             "  byte c;\n"
             "  initial c = s[2];\n"
             "endmodule\n"));
}

// The control the two above need. §11.5.1 leaves a bit-select of a scalar
// illegal, and a one-bit logic variable is such a scalar, so indexing one is
// still an error. Without this, an elaborator that simply stopped checking
// selects would satisfy both tests above while enforcing nothing.
TEST(Elaboration, IndexingAScalarLogicVarIsStillRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic s;\n"
      "  logic c;\n"
      "  initial c = s[2];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            4, "11.5.1"));
}

// §6.16's Table 6-9 (printed page 114) gives concatenation over string
// operands: string literals and expressions of string type may be mixed in
// one concatenation, and what it yields has string type. §11.2.1 counts
// parameters among the operands a constant expression may be built from, so
// `{P, "c"}` is one and Q holds the joined characters.
//
// The characters are read back rather than Q's resolved_value, which §11.10
// packs from the same expression and would answer whether or not §6.16 gave
// the concatenation a string result at all.
TEST(Elaboration, StringParameterConcatenationFoldsToTheJoinedCharacters) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  localparam string P = \"ab\";\n"
      "  localparam string Q = {P, \"c\"};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const auto* q = FindParam(design, "top", "Q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->resolved_string, "abc");
}

// The same concatenation written inside a generate block. §27.4 makes a
// generate block a scope of its own and a further level of hierarchy once
// instantiated, and §6.16 says nothing that would stop at that boundary, so the
// block's own P is what the concatenation names and Q holds the same three
// characters the module-level case above gives it.
//
// This fails while Elaborator::ProcessPendingGenerate in
// src/elaborator/elaborator_generate.cpp opens no ParamRangeRegistryGuard:
// StringParamChars in src/elaborator/const_eval.cpp answers from the
// registered module, there is none for the whole of a block's body, and the
// concatenation recovers no characters at all, leaving resolved_string empty.
TEST(Elaboration, StringParameterConcatenationFoldsInsideAGenerateBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam string P = \"ab\";\n"
      "      localparam string Q = {P, \"c\"};\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const auto* q = FindParam(design, "top", "Q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->resolved_string, "abc");
}

// §6.16 makes the string type and the integral types type-incompatible -- it
// gives conversion between them only through the string methods and the
// assignment rules of §6.16, and no implicit conversion -- so a direct
// assignment of an integral variable to a string variable is an error wherever
// the assignment is written. CheckStringNumericAssigns in
// src/elaborator/elaborator_scope_rules.cpp is the site enforcing it, and it
// had written out nine of the thirteen child-statement links Stmt declares. It
// now takes the list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h, and the five cases below cover
// one newly reached position each. A randsequence production keeps statements
// in RsProd::code_stmts and in RsRule::weight_code, which
// ForEachRandsequenceRuleStmt reaches by different members, so each is its own
// position.
//
// `stmt` is written at line 6 and may run to several lines, so the line the
// report stands at is read back out of the source rather than counted.
void ExpectStringNumericAssignIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n  string s;\n  int n;\n  logic ok;\n"
      "  initial\n    " +
      stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type-incompatible assignment between string and numeric type",
      LineHolding(src, "s = n;"), "6.16"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(Elaboration, StringNumericAssignInAnAssertionPassStmt) {
  ExpectStringNumericAssignIn("assert (ok) s = n;");
}

TEST(Elaboration, StringNumericAssignInAnAssertionFailStmt) {
  ExpectStringNumericAssignIn("assert (ok) else s = n;");
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §6.16 is a rule about the source, so it holds whether the weighted
// draw would select the item or not.
TEST(Elaboration, StringNumericAssignInARandcaseItem) {
  ExpectStringNumericAssignIn("randcase 1: s = n; endcase");
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(Elaboration, StringNumericAssignInARandsequenceCodeBlock) {
  ExpectStringNumericAssignIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { s = n; };\n"
      "      endsequence\n"
      "    end");
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it.
TEST(Elaboration, StringNumericAssignInARandsequenceWeightCodeBlock) {
  ExpectStringNumericAssignIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { s = n; };\n"
      "        alt : { ok = 1; };\n"
      "      endsequence\n"
      "    end");
}

// §6.16 needs a cast between a string and an integral value in either
// direction, whatever expression supplies the value: an integral literal, an
// operation on an integral variable, a real literal, an integral initializer
// of a module's or a block's string, a string written into one character of a
// string, and a string method's string result written to an integer are each
// reported. An element of an array of strings is a string, a method giving an
// integer, a comparison of strings and a string literal stand on neither side,
// and a structure's member, a call's result and a chandle are not read here.
TEST(Elaboration, UncastStringIntegralAssignmentOfAnyShapeReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {string a;} T;\n"
      "  int n = 1;\n"
      "  real r;\n"
      "  string s = \"ab\";\n"
      "  string t = n;\n"
      "  string sa[2];\n"
      "  int arr[];\n"
      "  T st;\n"
      "  chandle ch;\n"
      "  function automatic void f();\n"
      "    s = 8'h41;\n"
      "  endfunction\n"
      "  function automatic int g();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    string u;\n"
      "    string w = n;\n"
      "    s = n + 1;\n"
      "    s <= 1.5;\n"
      "    s[0] = t;\n"
      "    n = t.substr(0, 1);\n"
      "    sa[0] = t;\n"
      "    n = t.len();\n"
      "    arr = new[2];\n"
      "    n = arr.size();\n"
      "    n = g();\n"
      "    n = st.a[0];\n"
      "    n = (s == t);\n"
      "    s = \"x\";\n"
      "    ch = null;\n"
      "    n = r;\n"
      "  end\n"
      "endmodule\n",
      f);
  constexpr std::string_view kMessage =
      "type-incompatible assignment between string and numeric type";
  for (uint32_t line : {6U, 12U, 19U, 20U, 21U, 22U, 23U}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, line, "6.16"));
  }
  for (uint32_t line : {24U, 25U, 26U, 27U, 28U, 29U, 30U, 31U, 32U, 33U}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kMessage, line, "6.16"));
  }
}

}  // namespace
