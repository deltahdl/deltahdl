#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CaseMatchesElaboration, CaseMatchesWithGuardElaborates) {
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

// §12.6: "A constant expression pattern shall be of integral type."
TEST(PatternMatching, RealLiteralPatternRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int y;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    case(r) matches\n"
      "      1.5: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constant expression pattern shall be of integral type", 7, "12.6"));
}

// §12.6: same rule applied to the binary `matches` operator.
TEST(PatternMatching, RealLiteralPatternInMatchesOperatorRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    y = r matches 2.5;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constant expression pattern shall be of integral type", 6, "12.6"));
}

// §12.6: a string literal is not of integral type, so it is also rejected
// when used as a constant expression pattern.
TEST(PatternMatching, StringLiteralPatternRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  string s;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    s = \"hi\";\n"
      "    y = s matches \"hi\";\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constant expression pattern shall be of integral type", 6, "12.6"));
}

// §12.6: a constant expression pattern (11.2.1) may be a localparam, not just a
// literal. An integral localparam is of integral type and shall be accepted.
TEST(PatternMatching, LocalparamIntegralPatternAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int P = 5;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    case(x) matches\n"
      "      P: y = 8'd1;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.6: a constant expression pattern (11.2.1) may also be a module parameter.
// An integral parameter is of integral type and shall be accepted.
TEST(PatternMatching, ParameterIntegralPatternAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter int Q = 6);\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd6;\n"
      "    case(x) matches\n"
      "      Q: y = 8'd1;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.6: a constant expression pattern (11.2.1) may be a constant function
// call. An integral-returning function used as a pattern is of integral type
// and shall be accepted.
TEST(PatternMatching, ConstFunctionCallIntegralPatternAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  function automatic int cf(); return 5; endfunction\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    case(x) matches\n"
      "      cf(): y = 8'd1;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.6: integer literal pattern is integral and shall be accepted.
TEST(PatternMatching, IntegerLiteralPatternAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    case(x) matches\n"
      "      8'd5: y = 8'd1;\n"
      "      8'd6: y = 8'd2;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.6: "Pattern identifiers shall be unique in the pattern" — the same
// identifier cannot bind in more than one position of a single pattern. Here
// the structure pattern binds `r1` twice, which is rejected.
TEST(PatternMatching, DuplicatePatternIdentifierRejected) {
  SimFixture f;
  ElaborateSrc(
      "typedef union tagged { struct { bit [3:0] a, b; } Add; } u_t;\n"
      "module t;\n"
      "  u_t u;\n"
      "  int y;\n"
      "  initial\n"
      "    case (u) matches\n"
      "      tagged Add '{.r1, .r1}: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern identifier 'r1' is used more than once in "
                            "a single pattern",
                            7, "12.6"));
}

// §12.6: distinct pattern identifiers in a single pattern are allowed, so the
// uniqueness check does not over-reject a well-formed structure pattern.
TEST(PatternMatching, DistinctPatternIdentifiersAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "typedef union tagged { struct { bit [3:0] a, b; } Add; } u_t;\n"
      "module t;\n"
      "  u_t u;\n"
      "  int y;\n"
      "  initial\n"
      "    case (u) matches\n"
      "      tagged Add '{.r1, .r2}: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.6: the same uniqueness rule applies to a pattern used with the binary
// `matches` operator, not just a case item.
TEST(PatternMatching, DuplicatePatternIdentifierInMatchesOperatorRejected) {
  SimFixture f;
  ElaborateSrc(
      "typedef union tagged { struct { bit [3:0] a, b; } Add; } u_t;\n"
      "module t;\n"
      "  u_t u;\n"
      "  logic y;\n"
      "  initial y = u matches (tagged Add '{.r1, .r1});\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern identifier 'r1' is used more than once in "
                            "a single pattern",
                            5, "12.6"));
}

// §12.6: the report that refuses a non-integral constant expression pattern
// names the subclause stating the rule, so a caller learns which rule was
// enforced without matching the wording of the message.
TEST(PatternMatching, RealLiteralPatternNames12_6) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int y;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    case(r) matches\n"
      "      1.5: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constant expression pattern shall be of integral type", 7, "12.6"));
}

// §12.6 requires a constant expression pattern to be of integral type and puts
// no condition on where the pattern is written, so every position a statement
// holds a statement in is a position the report is made at.
// WalkStmtForMatchesPattern in
// src/elaborator/elaborator_validate_matches.cpp had written out eight of the
// thirteen child-statement links Stmt declares, and now takes the list from
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h. The cases
// below cover one newly reached position each. Each writes the pattern under
// the binary `matches` operator of §12.6, which stands in an ordinary
// expression and so can be written in a for initializer and a for step as well
// as in the four statement positions.

// §12.7.1's for loop holds its initialization statements in Stmt::for_inits,
// apart from its body.
TEST(PatternMatching, ARealLiteralPatternInAForInitializerIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic y;\n"
      "  integer i;\n"
      "  initial for (y = r matches 2.5; i < 2; i = i + 1) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constant expression pattern shall be of integral type", 5, "12.6"));
}

// Stmt::for_steps holds the same loop's step assignments, a member of its own
// beside the initializers.
TEST(PatternMatching, ARealLiteralPatternInAForStepIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic y;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 2; y = r matches 2.5) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constant expression pattern shall be of integral type", 5, "12.6"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(PatternMatching, ARealLiteralPatternInAnAssertionPassStatementIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic y;\n"
      "  logic ok;\n"
      "  initial assert (ok) y = r matches 2.5;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constant expression pattern shall be of integral type", 5, "12.6"));
}

TEST(PatternMatching, ARealLiteralPatternInAnAssertionFailStatementIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic y;\n"
      "  logic ok;\n"
      "  initial assert (ok) else y = r matches 2.5;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constant expression pattern shall be of integral type", 5, "12.6"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(PatternMatching, ARealLiteralPatternInARandsequenceCodeBlockIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { y = r matches 2.5; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constant expression pattern shall be of integral type", 6, "12.6"));
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it.
TEST(PatternMatching,
     ARealLiteralPatternInARandsequenceWeightCodeBlockIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic y;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { y = r matches 2.5; };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constant expression pattern shall be of integral type", 7, "12.6"));
}

}  // namespace
