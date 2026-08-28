#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

// §11.5.1 says of a non-indexed part-select `vect[msb_expr:lsb_expr]` that
// "The first expression shall address a more significant bit than the second
// expression", and states no condition on where the select stands. §11.5 makes
// a part-select an operand, so the rule is owed wherever an expression can be
// written, which is wherever a statement can be written. The four cases here
// each put one reversed part-select in one statement position.
//
// Each of those four is a position Elaborator::ValidatePartSelectBounds reached
// only once CheckPartSelectBoundsStmt in
// src/elaborator/elaborator_validate_queries_dims.cpp took its list of nested
// statements from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. Every one of them elaborated
// clean beforehand, with a reversed part-select left unreported.
//
// Every vector below is declared [7:4] rather than [7:0] so that an index and
// the storage offset it reaches are different numbers. On [7:0] the two
// coincide, and a check that computed an offset where §11.5.1 requires an index
// would answer such a case the same way the rule does, which
// docs/tenets/tests/UNIT_TESTS.md bars.

namespace {

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case covers
// the pass arm and the one below it the fail arm.
TEST(SelectElaboration,
     ReversedPartSelectInAnAssertionPassStatementNames11_5_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:4] v;\n"
      "  logic [3:0] result;\n"
      "  logic ok;\n"
      "  initial assert (ok) result = v[4:7];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 5,
                            "11.5.1"));
}

TEST(SelectElaboration,
     ReversedPartSelectInAnAssertionFailStatementNames11_5_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:4] word;\n"
      "  logic [3:0] out;\n"
      "  logic passed;\n"
      "  initial assert (passed) else out = word[4:7];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 5,
                            "11.5.1"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. §11.5.1's
// ordering rule is a static one, so it holds whether the weighted draw would
// select the item or not.
TEST(SelectElaboration, ReversedPartSelectInARandcaseItemNames11_5_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:4] bus;\n"
      "  logic [3:0] taken;\n"
      "  initial randcase 1: taken = bus[4:7]; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 4,
                            "11.5.1"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions.
TEST(SelectElaboration, ReversedPartSelectInARandsequenceCodeBlockNames11_5_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:4] src;\n"
      "  logic [3:0] dst;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { dst = src[4:7]; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 6,
                            "11.5.1"));
}

}  // namespace
