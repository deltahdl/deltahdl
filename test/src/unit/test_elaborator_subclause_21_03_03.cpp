#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §21.3.3: the first argument to $swrite (and the output variable of $sformat)
// shall be a variable of an integral, unpacked-array-of-byte, or string type.
// A string-typed destination is the canonical accepting form and elaborates.
TEST(StringFormatTaskElaboration, SwriteStringOutputVarAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial $swrite(s, \"x=%0d\", 7);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §21.3.3: an integral destination is an admitted form of the output-variable
// rule. Built from a real packed-vector declaration so elaboration resolves the
// reference and accepts the call.
TEST(StringFormatTaskElaboration, SwriteIntegralOutputVarAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] v;\n"
      "  initial $swrite(v, \"%h\", 8'hab);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §21.3.3: an unpacked array of byte is an admitted output-variable form. Built
// from a real unpacked-array declaration so elaboration resolves the reference
// and accepts the call rather than rejecting it as a disallowed type.
TEST(StringFormatTaskElaboration, SwriteUnpackedByteArrayOutputVarAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b [0:3];\n"
      "  initial $swrite(b, \"ABCD\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §21.3.3 negative form: the output variable "shall be a variable of integral,
// unpacked array of byte, or string data types" -- a real destination has no
// character representation and is the closest illegal form. $swrite into a real
// variable shall be rejected.
TEST(StringFormatTaskElaboration, SwriteRealOutputVarRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  initial $swrite(r, \"x=%0d\", 7);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the output variable of $swrite/$sformat shall be "
                            "of an integral, unpacked array of byte, or string "
                            "type, not real",
                            3, "21.3.3"));
}

// §21.3.3 negative form for $sformat: its output variable is subject to the
// same rule, so a real destination is likewise rejected.
TEST(StringFormatTaskElaboration, SformatRealOutputVarRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  initial $sformat(r, \"v=%0d\", 3);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the output variable of $swrite/$sformat shall be "
                            "of an integral, unpacked array of byte, or string "
                            "type, not real",
                            3, "21.3.3"));
}

// §21.3.3: $sformatf takes no output variable -- its first argument is the
// format string and its result is the function return value. A real target for
// the RESULT (assigned from the function value) is a different rule and must
// not trip the output-variable check; the format-only call elaborates cleanly.
TEST(StringFormatTaskElaboration, SformatfHasNoOutputVarCheck) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial s = $sformatf(\"val=%0d\", 42);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §21.3.3 states its rule over the first argument of $swrite and $sformat --
// it "shall be a variable of integral, unpacked array of byte, or string data
// types" -- and names no position the call may stand in. Each of the four
// cases below writes the call in one such position, and each is a position
// CheckStringOutputTargetsStmt in
// src/elaborator/elaborator_validate_queries.cpp reached only once it took its
// list of nested statements from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. Every one of them elaborated
// clean beforehand, with a real variable left as the destination of a
// formatted string.
//
// Stmt::for_steps is the fifth position that list added and it carries no case
// here. Both tasks return no value, so neither stands in the
// operator_assignment or the inc_or_dec_expression A.6.8 admits as a
// for_step_assignment; and Syntax 21-6 writes both of them with a terminating
// semicolon -- `string_output_tasks ::= string_output_task_name ( output_var
// [ , list_of_arguments ] ) ;` and the same for $sformat -- while writing
// $sformatf, the function of the same family, without one. A
// function_subroutine_call in a for_step carries no semicolon either.

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm.
// The parser keeps the pass arm in Stmt::assert_pass_stmt.
TEST(StringFormatTaskElaboration,
     SwriteRealOutputVarInAnAssertionPassStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real acc;\n"
      "  logic ready;\n"
      "  initial assert (ready) $swrite(acc, \"n=%0d\", 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the output variable of $swrite/$sformat shall be",
                            4, "21.3.3"));
}

// §16.3's else arm of the same action block, kept in Stmt::assert_fail_stmt.
// $sformat carries the same output-variable rule as the $swrite family, so the
// case names it rather than repeating the task above.
TEST(StringFormatTaskElaboration,
     SformatRealOutputVarInAnAssertionFailStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real tally;\n"
      "  logic done;\n"
      "  initial assert (done) else $sformat(tally, \"t=%0d\", 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the output variable of $swrite/$sformat shall be",
                            4, "21.3.3"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. Syntax
// 21-6's string_output_task_name admits $swriteb, so the rejection also
// witnesses that the binary member of the family carries the rule.
TEST(StringFormatTaskElaboration, SwritebRealOutputVarInARandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real gauge;\n"
      "  initial randcase 3: $swriteb(gauge, \"%b\", 4'b1010); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the output variable of $swrite/$sformat shall be",
                            3, "21.3.3"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions. $swriteh is the hexadecimal member of Syntax 21-6's
// string_output_task_name.
TEST(StringFormatTaskElaboration,
     SwritehRealOutputVarInARandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real level;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { $swriteh(level, \"%h\", 8'hab); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the output variable of $swrite/$sformat shall be",
                            5, "21.3.3"));
}

}  // namespace
