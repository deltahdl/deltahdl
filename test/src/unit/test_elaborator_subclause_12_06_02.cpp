#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IfMatchesElaboration, IfMatchesElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    if (x matches 8'd5) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IfMatchesElaboration, IfMatchesWithGuardElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    en = 1'b1;\n"
      "    if (x matches 8'd5 &&& en) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.6.2: in each `e matches p` clause of an if-else predicate, e and p shall
// have the same statically known type. A real-valued left side cannot share a
// type with an integral constant pattern, so the pairing is a static error.
TEST(IfMatchesElaboration, RealValueWithIntegralPatternRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    r = 1.0;\n"
      "    if (r matches 8'd5) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs",
                            6, "12.6.2"));
}

// §12.6.2: the predicate is a sequential conjunction of clauses joined by
// `&&&`, so the per-clause type check reaches a matches clause that sits to the
// left of a Boolean filter as well.
TEST(IfMatchesElaboration,
     RealValueWithIntegralPatternInGuardedClauseRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    r = 1.0;\n"
      "    en = 1'b1;\n"
      "    if (r matches 8'd5 &&& en) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs",
                            8, "12.6.2"));
}

// §12.6.2: the per-clause same-type check applies to every matches clause of
// the predicate, so it must reach a matches clause that sits to the right of a
// leading Boolean filter as well as one on the left. Here the real-valued left
// side of the trailing matches clause cannot share a type with the integral
// pattern, so the pairing is a static error.
TEST(IfMatchesElaboration, RealValueMatchesInTrailingClauseRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    r = 1.0;\n"
      "    en = 1'b1;\n"
      "    if (en &&& r matches 8'd5) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs",
                            8, "12.6.2"));
}

// §12.6.2 requires each `e matches p` clause of an if-else predicate to pair a
// value and a pattern of one type, and puts no condition on where that if
// statement stands. CheckMatchesIfPredicateStmt in
// src/elaborator/elaborator_validate_matches.cpp had written out seven of the
// thirteen child-statement links Stmt declares, and now takes the list from
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h. The cases
// below cover one newly reached position each. Stmt::for_inits and
// Stmt::for_steps are the two remaining ones and get no case: A.6.8 admits only
// a variable assignment or a declaration there, so an if statement cannot be
// written in either.

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(IfMatchesElaboration, RealValueInAnAssertionPassStatementIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  logic ok;\n"
      "  initial assert (ok) if (r matches 8'd5) y = 8'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs",
                            5, "12.6.2"));
}

TEST(IfMatchesElaboration, RealValueInAnAssertionFailStatementIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  logic ok;\n"
      "  initial assert (ok) else if (r matches 8'd5) y = 8'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs",
                            5, "12.6.2"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, kept in
// Stmt::randcase_items. §12.6.2 is a rule about the source, so it holds whether
// the weighted draw would select the item or not.
TEST(IfMatchesElaboration, RealValueInARandcaseItemIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  initial randcase 1: if (r matches 8'd5) y = 8'd1; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs",
                            4, "12.6.2"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(IfMatchesElaboration, RealValueInARandsequenceCodeBlockIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { if (r matches 8'd5) y = 8'd1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs",
                            6, "12.6.2"));
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it.
TEST(IfMatchesElaboration, RealValueInARandsequenceWeightCodeBlockIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { if (r matches 8'd5) y = 8'd1; };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs",
                            7, "12.6.2"));
}

}  // namespace
