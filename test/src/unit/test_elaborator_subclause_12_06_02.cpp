#include <gtest/gtest.h>

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

// §12.6.2 gives a pattern identifier of an if statement's predicate the later
// clauses and the true arm as its scope, so the else arm reading the name
// reads no declaration and is §23.9's unresolved reference. A later clause
// reads a name an earlier one binds.
TEST(IfMatchesElaboration, PatternIdentifierReadInTheElseArmIsUnresolved) {
  SimFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt v; int y;\n"
      "  initial begin\n"
      "    if (v matches tagged Valid .n &&& n > 0) y = n;\n"
      "    else y = n;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'n'", 6,
                            "23.9"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

// §12.6 declares a pattern identifier as a new variable, and §12.6.2 makes the
// if's true arm part of its scope, so an assignment there writes it (#6415).
TEST(IfMatchesElaboration, AssignmentToPatternIdentifierInTrueArm) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { bit [3:0] Bt; int I; } U;\n"
      "  U u = tagged Bt 4'd3;\n"
      "  initial if (u matches tagged Bt .b) begin\n"
      "    b = 4'd5;\n"
      "    $display(\"%0d\", b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The false arm stands outside that scope, so `b` there names nothing.
TEST(IfMatchesElaboration,
     AssignmentToPatternIdentifierInFalseArmIsUndeclared) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { bit [3:0] Bt; int I; } U;\n"
      "  U u = tagged Bt 4'd3;\n"
      "  initial if (u matches tagged Bt .b) $display(\"%0d\", b);\n"
      "  else b = 4'd5;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'b'",
                            5, "23.9"));
}

// A method call through a pattern identifier, in the if's true arm, in a
// later `&&&` clause of its predicate and in a conditional expression's
// second operand (§12.6.3), names that variable and no hierarchical name
// (#6416).
TEST(IfMatchesElaboration, MethodCallThroughPatternIdentifier) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {A, B} E;\n"
      "  typedef union tagged { E En; int I; } U;\n"
      "  U u = tagged En B;\n"
      "  string s;\n"
      "  initial begin\n"
      "    if (u matches tagged En .ev) $display(\"%s\", ev.name());\n"
      "    if (u matches tagged En .e2 &&& e2.name() == \"B\") s = \"y\";\n"
      "    s = (u matches tagged En .e3) ? e3.name() : \"\";\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Outside that scope, in the false arm, the same name heads a hierarchical
// name that resolves to nothing.
TEST(IfMatchesElaboration, MethodCallThroughPatternIdentifierInFalseArm) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef enum {A, B} E;\n"
      "  typedef union tagged { E En; int I; } U;\n"
      "  U u = tagged En B;\n"
      "  initial if (u matches tagged En .ev) $display(\"%s\", ev.name());\n"
      "  else $display(\"%s\", ev.name());\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 'ev' resolves to no declaration",
                            6, "23.8"));
}

}  // namespace
