#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CaseMatchesItemElaboration, CaseMatchesItemElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    case(x) matches\n"
      "      8'd5: y = 8'd10;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CaseMatchesItemElaboration, CaseMatchesGuardElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic guard;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    guard = 1'b1;\n"
      "    case(x) matches\n"
      "      8'd5 &&& guard: y = 8'd10;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.6.1: the tested expression shall have a known type that is the same as
// the type of the pattern in each case item. A real-valued selector cannot
// share a type with an integral constant pattern, so the pairing is rejected.
TEST(CaseMatchesItemElaboration, RealSelectorWithIntegralPatternRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    r = 1.0;\n"
      "    case(r) matches\n"
      "      8'd5: y = 8'd10;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching case selector type differs", 6,
                            "12.6.1"));
}

// §12.6.1: the type check looks through a `&&&` filter to the pattern itself,
// so a real selector paired with a guarded integral pattern is still rejected.
TEST(CaseMatchesItemElaboration,
     RealSelectorWithGuardedIntegralPatternRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    r = 1.0;\n"
      "    en = 1'b1;\n"
      "    case(r) matches\n"
      "      8'd5 &&& en: y = 8'd10;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching case selector type differs", 8,
                            "12.6.1"));
}

// §12.6.1 requires the tested expression of a pattern-matching case statement
// to share a type with its patterns, and puts no condition on where that case
// statement stands. CheckMatchesCaseSelectorType in
// src/elaborator/elaborator_validate_matches.cpp had written out seven of the
// thirteen child-statement links Stmt declares, and now takes the list from
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h. The cases
// below cover one newly reached position each. Stmt::for_inits and
// Stmt::for_steps are the two remaining ones and get no case: A.6.8 admits only
// a variable assignment or a declaration there, so a case statement cannot be
// written in either.

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(CaseMatchesItemElaboration,
     RealSelectorInAnAssertionPassStatementIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  logic ok;\n"
      "  initial assert (ok)\n"
      "    case (r) matches\n"
      "      8'd5: y = 8'd10;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching case selector type differs", 6,
                            "12.6.1"));
}

TEST(CaseMatchesItemElaboration,
     RealSelectorInAnAssertionFailStatementIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  logic ok;\n"
      "  initial assert (ok) else\n"
      "    case (r) matches\n"
      "      8'd5: y = 8'd10;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching case selector type differs", 6,
                            "12.6.1"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, kept in
// Stmt::randcase_items. §12.6.1 is a rule about the source, so it holds whether
// the weighted draw would select the item or not.
TEST(CaseMatchesItemElaboration, RealSelectorInARandcaseItemIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  initial randcase\n"
      "    1:\n"
      "      case (r) matches\n"
      "        8'd5: y = 8'd10;\n"
      "      endcase\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching case selector type differs", 6,
                            "12.6.1"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(CaseMatchesItemElaboration,
     RealSelectorInARandsequenceCodeBlockIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : {\n"
      "        case (r) matches\n"
      "          8'd5: y = 8'd10;\n"
      "        endcase\n"
      "      };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching case selector type differs", 7,
                            "12.6.1"));
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it.
TEST(CaseMatchesItemElaboration,
     RealSelectorInARandsequenceWeightCodeBlockIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 {\n"
      "        case (r) matches\n"
      "          8'd5: y = 8'd10;\n"
      "        endcase\n"
      "      };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching case selector type differs", 8,
                            "12.6.1"));
}

}  // namespace
