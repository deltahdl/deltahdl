#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §16.14.3: a cover statement's optional pass statement (statement_or_null)
// shall not include any concurrent assert, assume, or cover statement. The
// behavior depends on how the pass statement is produced — the parser turns a
// procedural concurrent assertion into an assert/assume/cover Stmt carrying the
// is_procedural_concurrent flag, which an ordinary or immediate statement never
// sets — so each test builds a real cover statement and drives it through
// parse + elaborate, observing whether the elaborator flags the pass statement.
// ValidateClockingBlock is a no-op for a cover item, so the only diagnostic a
// cover statement can raise here is this rule, and f.has_errors isolates it.

// Common declarations; each test appends a cover statement and `endmodule`.
constexpr const char* kDecls =
    "module m;\n"
    "  logic clk, a, b;\n";

// Control: a cover property whose pass statement is an ordinary statement
// elaborates cleanly — the well-formed baseline the rejections are measured
// against.
TEST(CoverPassStatement, OrdinaryPassStatementIsAccepted) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a) $display(\"hit\");\n"
                   "endmodule\n",
               f);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.3: a concurrent assert statement standing as the pass statement is
// rejected.
TEST(CoverPassStatement, RejectsConcurrentAssertPassStatement) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    assert property (@(posedge clk) b);\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

// §16.14.3: a concurrent assume statement standing as the pass statement is
// rejected.
TEST(CoverPassStatement, RejectsConcurrentAssumePassStatement) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    assume property (@(posedge clk) b);\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

// §16.14.3: a concurrent cover statement standing as the pass statement is
// rejected.
TEST(CoverPassStatement, RejectsConcurrentCoverPassStatement) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    cover property (@(posedge clk) b);\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

// §16.14.3: the prohibition is on any *included* concurrent assertion, not only
// one written directly — a concurrent assert buried inside a begin-end block
// that serves as the pass statement is still rejected.
TEST(CoverPassStatement, RejectsConcurrentAssertNestedInBlock) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a) begin\n"
                   "    assert property (@(posedge clk) b);\n"
                   "  end\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

// §16.14.3: "include" reaches a concurrent assertion in the then-branch of an
// if statement standing as the pass statement.
TEST(CoverPassStatement, RejectsConcurrentAssertNestedInIfThen) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    if (a) assert property (@(posedge clk) b);\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

// §16.14.3: "include" likewise reaches a concurrent assertion in the
// else-branch of an if statement — the then-branch here is an ordinary
// statement.
TEST(CoverPassStatement, RejectsConcurrentAssertNestedInIfElse) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    if (a) $display(\"x\");\n"
                   "    else assert property (@(posedge clk) b);\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

// §16.14.3: "include" reaches a concurrent assertion in the body of a for loop
// standing as the pass statement.
TEST(CoverPassStatement, RejectsConcurrentAssertNestedInForLoop) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    for (int i = 0; i < 2; i = i + 1)\n"
                   "      assert property (@(posedge clk) b);\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

// §16.14.3: "include" reaches a concurrent assertion nested inside a fork-join
// that serves as the pass statement.
TEST(CoverPassStatement, RejectsConcurrentAssertNestedInFork) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    fork assert property (@(posedge clk) b); join\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

// §16.14.3: the rule bars *concurrent* assertions only. An immediate assertion
// is a permitted pass statement, so it does not trigger the diagnostic.
TEST(CoverPassStatement, AllowsImmediateAssertPassStatement) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a) assert (b);\n"
                   "endmodule\n",
               f);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.3: the same prohibition governs a cover sequence statement's pass
// statement.
TEST(CoverPassStatement, RejectsConcurrentAssertInCoverSequencePassStatement) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover sequence (@(posedge clk) a ##1 b)\n"
                   "    assert property (@(posedge clk) b);\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

// §16.14.3: a cover sequence with an ordinary pass statement is accepted.
TEST(CoverPassStatement, CoverSequenceOrdinaryPassStatementIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      std::string(kDecls) +
          "  cover sequence (@(posedge clk) a ##1 b) $display(\"m\");\n"
          "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.3: "include" reaches a concurrent assertion in an arm of a randcase
// statement standing as the pass statement. A.6.7 gives
// `randcase_item ::= expression : statement_or_null`, so an arm holds any
// statement the pass statement itself could hold. Stmt::randcase_items is one
// of the four links FindConcurrentAssertionInPassStmt in
// src/elaborator/elaborator_items_assertions.cpp did not descend before it was
// given ForEachChildStmt, so this assertion was not found.
TEST(CoverPassStatement, RejectsConcurrentAssertInRandcaseArm) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    randcase\n"
                   "      1: assert property (@(posedge clk) b);\n"
                   "    endcase\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

// §16.14.3: "include" reaches a concurrent assertion in the code block of a
// randsequence production standing as the pass statement. A.6.12 gives
// `rs_code_block ::= { { data_declaration } { statement_or_null } }`, so a code
// block holds any statement the pass statement itself could hold.
// Stmt::rs_productions is the second of the four links the walk did not
// descend.
TEST(CoverPassStatement, RejectsConcurrentAssertInRandsequenceCodeBlock) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    randsequence (main)\n"
                   "      main : { assert property (@(posedge clk) b); };\n"
                   "    endsequence\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

// The other two links FindConcurrentAssertionInPassStmt gained get no case,
// because no conforming source can put a concurrent assertion in either.
//
// Stmt::for_inits: A.6.8 gives
// `for_initialization ::= list_of_variable_assignments |
// for_variable_declaration { , for_variable_declaration }`, and both
// alternatives are assignments or declarations. No production reaches
// statement_or_null there, so a `for` header holds no assertion statement to
// find.
//
// Stmt::for_steps: A.6.8 gives
// `for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call`, which is the same finding. Neither omission was
// reachable from a conforming cover statement; they were carried because the
// walk wrote out its own list rather than reading ForEachChildStmt's.

}  // namespace
