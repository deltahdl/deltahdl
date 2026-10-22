#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssignmentPatternElaboration, ReplicationPatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0][7:0] x;\n"
      "  initial begin\n"
      "    x = '{4{8'hAB}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, IntegerAtomTypePatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = int'{42};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, ConstantAssignmentPatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int arr [3] = '{10, 20, 30};\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, TypeReferencePatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0][7:0] x;\n"
      "  initial x = type(x)'{8'd1, 8'd2};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, LhsPositionalPatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial '{a, b} = 16'hABCD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, TypedPatternExpressionInPortIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module sub(input int a);\n"
      "endmodule\n"
      "module top;\n"
      "  sub u(.a(int'{42}));\n"
      "endmodule\n",
      f);
  // §10.9: a typed pattern has a type of its own and stands wherever an
  // expression may, a port connection at an instantiation among the places;
  // only a port expression of a declaration is barred.
  EXPECT_EQ(FindDiag(f, "an assignment pattern cannot be connected"), nullptr);
}

TEST(AssignmentPatternElaboration, ErrorLhsNamedKeys) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  logic [7:0] x, y;\n"
      "  initial '{a: x, b: y} = p;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 5, "10.9"));
}

TEST(AssignmentPatternElaboration, ErrorNonConstantInConstantPattern) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  localparam int arr [3] = '{x, 2, 3};\n"
      "endmodule\n",
      f);
  // The rule reported is §6.20.4's, not §10.9's: the pattern's non-constant
  // member is caught as a non-constant localparam initializer.
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "localparam 'arr' initializer is not a constant expression",
                    3, "6.20.4"));
}

// §10.9 footnote 37: the members of a constant assignment pattern shall be
// constant expressions. A named parameter is a constant expression (11.2.1) and
// resolves through a different const-eval path than a literal token, so the
// accepting path is exercised here with parameter members.
TEST(AssignmentPatternElaboration, ConstantPatternWithParameterMembers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int A = 10;\n"
      "  parameter int B = 20;\n"
      "  localparam int arr [2] = '{A, B};\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.9 footnote 37: a localparam is likewise a constant expression and is a
// distinct constant form from both a literal and a parameter; the accepting
// path is exercised here with localparam members.
TEST(AssignmentPatternElaboration, ConstantPatternWithLocalparamMembers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int A = 5;\n"
      "  localparam int arr [2] = '{A, A};\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, ExpressionUsableOutsideAssignmentSide) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial x = int'{40} + 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, ErrorTypedLhsPatternNamedKeys) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  logic [7:0] x, y;\n"
      "  initial pair_t'{a: x, b: y} = p;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 5, "10.9"));
}

TEST(AssignmentPatternElaboration, ErrorLhsPatternBitCountMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial '{a, b} = 32'hDEADBEEF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 3,
      "10.9"));
}

// §10.9 says a left-hand-side assignment pattern is written in positional
// notation and holds as many bits as the right-hand side supplies, and puts no
// condition on where the assignment stands. Every position a statement holds a
// statement in is therefore a position both rules are reported at.
// WalkStmtsForLhsPatternKeys and WalkStmtsForLhsPatternWidths in
// src/elaborator/elaborator_validate_matches.cpp had each written out six of
// the thirteen child-statement links Stmt declares, so an assignment written in
// any of the other seven was exempt from §10.9. Both walks now take the list
// from ForEachChildStmt in src/elaborator/elaborator_validate_internal.h, and
// the cases below cover one newly reached position each. The seven links make
// eight positions because ForEachRandsequenceRuleStmt reaches a randsequence
// production's two statement lists by different members.

// §9.3.2's fork-join keeps its statements in Stmt::fork_stmts, a member neither
// walk visited.
TEST(AssignmentPatternElaboration, AKeyedLhsPatternInsideForkIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  logic [15:0] p;\n"
      "  initial fork\n"
      "    '{0: x, 1: y} = p;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 5, "10.9"));
}

// §12.7.1's for loop holds its initialization statements in Stmt::for_inits,
// and A.6.8 gives a variable_assignment there whose left-hand side may be an
// assignment pattern like any other.
TEST(AssignmentPatternElaboration,
     AKeyedLhsPatternInAForInitializerIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  logic [15:0] p;\n"
      "  integer i;\n"
      "  initial for ('{0: x, 1: y} = p; i < 2; i = i + 1) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 5, "10.9"));
}

// Stmt::for_steps holds the same loop's step assignments, a member of its own
// beside the initializers.
TEST(AssignmentPatternElaboration, AKeyedLhsPatternInAForStepIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  logic [15:0] p;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 2; '{0: x, 1: y} = p) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 5, "10.9"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(AssignmentPatternElaboration,
     AKeyedLhsPatternInAnAssertionPassStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  logic [15:0] p;\n"
      "  logic ok;\n"
      "  initial assert (ok) '{0: x, 1: y} = p;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 5, "10.9"));
}

TEST(AssignmentPatternElaboration,
     AKeyedLhsPatternInAnAssertionFailStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  logic [15:0] p;\n"
      "  logic ok;\n"
      "  initial assert (ok) else '{0: x, 1: y} = p;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 5, "10.9"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, kept in
// Stmt::randcase_items. §10.9 is a rule about the source, so it holds whether
// the weighted draw would select the item or not.
TEST(AssignmentPatternElaboration, AKeyedLhsPatternInARandcaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  logic [15:0] p;\n"
      "  initial randcase 1: '{0: x, 1: y} = p; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 4, "10.9"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(AssignmentPatternElaboration,
     AKeyedLhsPatternInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  logic [15:0] p;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { '{0: x, 1: y} = p; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 6, "10.9"));
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it.
TEST(AssignmentPatternElaboration,
     AKeyedLhsPatternInARandsequenceWeightCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  logic [15:0] p;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { '{0: x, 1: y} = p; };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 7, "10.9"));
}

// The eight cases below put the bit-count rule of §10.9 at the same eight
// positions. It is enforced by WalkStmtsForLhsPatternWidths, a second walk with
// a list of its own, so a position covered for the keyed-notation rule says
// nothing about whether this one reaches it.
TEST(AssignmentPatternElaboration, AMissizedLhsPatternInsideForkIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial fork\n"
      "    '{a, b} = 32'hDEADBEEF;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 4,
      "10.9"));
}

TEST(AssignmentPatternElaboration,
     AMissizedLhsPatternInAForInitializerIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  integer i;\n"
      "  initial for ('{a, b} = 32'hDEADBEEF; i < 2; i = i + 1) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 4,
      "10.9"));
}

TEST(AssignmentPatternElaboration, AMissizedLhsPatternInAForStepIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 2; '{a, b} = 32'hDEADBEEF) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 4,
      "10.9"));
}

TEST(AssignmentPatternElaboration,
     AMissizedLhsPatternInAnAssertionPassStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  logic ok;\n"
      "  initial assert (ok) '{a, b} = 32'hDEADBEEF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 4,
      "10.9"));
}

TEST(AssignmentPatternElaboration,
     AMissizedLhsPatternInAnAssertionFailStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  logic ok;\n"
      "  initial assert (ok) else '{a, b} = 32'hDEADBEEF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 4,
      "10.9"));
}

TEST(AssignmentPatternElaboration,
     AMissizedLhsPatternInARandcaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial randcase 1: '{a, b} = 32'hDEADBEEF; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 3,
      "10.9"));
}

TEST(AssignmentPatternElaboration,
     AMissizedLhsPatternInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { '{a, b} = 32'hDEADBEEF; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 5,
      "10.9"));
}

TEST(AssignmentPatternElaboration,
     AMissizedLhsPatternInARandsequenceWeightCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { '{a, b} = 32'hDEADBEEF; };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 6,
      "10.9"));
}

// §10.9 states the left-hand-side pattern rules wherever the assignment
// stands: positional notation, and the bit count the right-hand side supplies.
TEST(AssignmentPatternElaboration, LhsPatternRulesReachFunctionBodies) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  function void fn();\n"
      "    '{0: a, 1: b} = 16'h0;\n"
      "    '{a, b} = 32'h0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 4, "10.9"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 5,
      "10.9"));
}

// §10.8 makes a continuous assignment an assignment-like context, so a pattern
// on its left-hand side is positional too.
TEST(AssignmentPatternElaboration, KeyedLhsPatternInContAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  assign '{0: a, 1: b} = 16'h0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 3, "10.9"));
}

// §10.9: an untyped pattern is one side of an assignment-like context only
// when the other side has a self-determined type, which another untyped
// pattern does not; a typed pattern gives the other side its type.
TEST(AssignmentPatternElaboration, UntypedPatternOnBothSidesIsError) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct packed { logic [7:0] x, y; } xy_t;\n"
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial '{a, b} = '{8'd1, 8'd2};\n"
      "  initial xy_t'{a, b} = '{8'd1, 8'd2};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment between two untyped assignment "
                            "patterns gives neither a type",
                            4, "10.9"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "an assignment between two untyped assignment "
                             "patterns gives neither a type",
                             5, "10.9"));
}

// §10.9: the bit count a left-hand-side pattern needs is checked against a
// right-hand side that is a name, a select of a vector or a call, whose widths
// the declarations give.
TEST(AssignmentPatternElaboration, LhsPatternBitCountAgainstNamedRhs) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b; logic [31:0] p; logic [3:0] mem [2];\n"
      "  function logic [23:0] g(); return 0; endfunction\n"
      "  initial begin\n"
      "    '{a, b} = p;\n"
      "    '{a, b} = p[23:0];\n"
      "    '{a, b} = g();\n"
      "    '{a, b} = p[15:0];\n"
      "    '{a, b} = mem[1];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 5,
      "10.9"));
  for (uint32_t line : {6u, 7u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "LHS assignment pattern needs 16 bits but RHS supplies 24 bits", line,
        "10.9"));
  }
  EXPECT_EQ(FindDiag(f, "but RHS supplies 4 bits"), nullptr);
}

// §10.9 (printed page 261): an unpacked array on the right of a positional
// pattern supplies the bits of every element, so under `typedef byte U[3]`,
// `U'{a, b, c} = A` takes A's three bytes and two items fall 8 bits short of
// them, and a byte array of two by two supplies 32 bits. A queue's element
// count is the run's to know, so the pattern it supplies is not sized here.
TEST(AssignmentPatternElaboration, LhsPatternBitCountAgainstAnUnpackedArray) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef byte U[3];\n"
      "  U A; byte a, b, c; byte sq [2][2]; byte q[$];\n"
      "  initial begin\n"
      "    U'{a, b, c} = A;\n"
      "    '{a, b} = A;\n"
      "    '{a, b, c} = sq;\n"
      "    '{a, b, c} = q;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 24 bits", 6,
      "10.9"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 24 bits but RHS supplies 32 bits", 7,
      "10.9"));
  for (uint32_t line : {5u, 8u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "LHS assignment pattern needs", line, "10.9"));
  }
}

// §10.9 (printed page 261): each item of a typed left-hand-side pattern has
// the bit count of the member of its type it stands for, so items whose widths
// are swapped against the members are reported though their total agrees.
TEST(AssignmentPatternElaboration, TypedLhsPatternItemWidthMismatchIsError) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct packed { logic [3:0] x; logic [11:0] y; } pair_t;\n"
      "module m;\n"
      "  logic [11:0] y4; logic [3:0] x12;\n"
      "  initial pair_t'{y4, x12} = 16'h0;\n"
      "  initial pair_t'{x12, y4} = 16'h0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "LHS assignment pattern item has 12 bits but "
                            "member 'x' of its type has 4 bits",
                            4, "10.9"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "LHS assignment pattern item has", 5, "10.9"));
}

// §10.9 lets an untyped pattern stand only as one side of an assignment-like
// context (§10.8), and an if or ?: condition, a vector concatenation item and
// a select index are none.
TEST(AssignmentPatternElaboration,
     UntypedPatternInNonAssignmentPositionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, v; logic [15:0] c;\n"
      "  initial begin\n"
      "    if ('{1}) a = 1;\n"
      "    a = '{1} ? 8'd1 : 8'd2;\n"
      "    c = {'{8'd1}, a};\n"
      "    a = v['{0}];\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4u, 5u, 6u, 7u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "assignment pattern without a type prefix "
                              "outside an assignment-like context",
                              line, "10.9"));
  }
}

}  // namespace
