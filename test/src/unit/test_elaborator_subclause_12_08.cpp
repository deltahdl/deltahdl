#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(JumpStatementElaboration, BreakInsideForLoopOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) begin\n"
      "      if (i == 5) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ContinueInsideWhileLoopOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    int i = 0;\n"
      "    while (i < 10) begin\n"
      "      i = i + 1;\n"
      "      if (i == 5) continue;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, BreakOutsideLoopInInitialIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    break;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "break statement is not inside a loop", 3, "12.8"));
}

TEST(JumpStatementElaboration, ContinueOutsideLoopInAlwaysIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  always @(posedge clk) begin\n"
      "    continue;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "continue statement is not inside a loop", 4,
                            "12.8"));
}

TEST(JumpStatementElaboration, BreakOutsideLoopInsideIfInInitialIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic done;\n"
      "  initial begin\n"
      "    if (done) break;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "break statement is not inside a loop", 4, "12.8"));
}

TEST(JumpStatementElaboration, ContinueOutsideLoopInFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    continue;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "continue statement is not inside a loop", 3,
                            "12.8"));
}

TEST(JumpStatementElaboration, BreakInForkInsideLoopIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic done;\n"
      "  initial begin\n"
      "    forever begin\n"
      "      fork\n"
      "        begin\n"
      "          if (done) break;\n"
      "        end\n"
      "      join\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "break inside fork-join cannot exit a loop outside the fork-join block",
      7, "12.8"));
}

TEST(JumpStatementElaboration, ContinueInForkInsideLoopIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic skip;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 8; i++) begin\n"
      "      fork\n"
      "        begin\n"
      "          if (skip) continue;\n"
      "        end\n"
      "      join\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "continue inside fork-join cannot affect a loop "
                            "outside the fork-join block",
                            7, "12.8"));
}

TEST(JumpStatementElaboration, BreakInLoopInsideForkOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic done;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        forever begin\n"
      "          if (done) break;\n"
      "        end\n"
      "      end\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ContinueInLoopInsideForkOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic skip;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        for (int i = 0; i < 8; i++) begin\n"
      "          if (skip) continue;\n"
      "        end\n"
      "      end\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnInInitialIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    return;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return statement is only allowed inside a "
                            "subroutine",
                            3, "12.8"));
}

TEST(JumpStatementElaboration, ReturnInsideFunctionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int square(int v);\n"
      "    return v * v;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, BareReturnInVoidFunctionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void touch();\n"
      "    return;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, BareReturnInValueReturningFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int compute();\n"
      "    return;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return statement in non-void function 'compute' "
                            "shall have an expression",
                            3, "12.8"));
}

TEST(JumpStatementElaboration, ReturnInsideTaskOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task do_thing();\n"
      "    return;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnStringLiteralFromIntFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int compute();\n"
      "    return \"hello\";\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'compute' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            3, "12.8"));
}

TEST(JumpStatementElaboration, ReturnIntegerLiteralFromIntFunctionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int compute();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Claim 8, string operand type in the accepting position: a string-returning
// function may return a string literal.
TEST(JumpStatementElaboration, ReturnStringLiteralFromStringFunctionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function string greet();\n"
      "    return \"hello\";\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Claim 8, real operand type in the accepting position: a real-returning
// function may return a real literal.
TEST(JumpStatementElaboration, ReturnRealLiteralFromRealFunctionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function real scale();\n"
      "    return 1.5;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Claim 8, negative form for a non-integral pairing: a real literal is not
// assignment-compatible with a string return type, so the return is rejected.
TEST(JumpStatementElaboration, ReturnRealLiteralFromStringFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function string name();\n"
      "    return 3.14;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'name' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            3, "12.8"));
}

TEST(JumpStatementElaboration, BreakInsideForeachOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr[4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) begin\n"
      "      if (arr[i] == 0) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §18.17.6 "Aborting productions—break and return" gives break and return a
// meaning inside a randsequence production code block that §12.8 does not:
// break "forces a jump out of the randsequence block" and return "aborts the
// generation of the current production". Neither needs the enclosing loop or
// the enclosing subroutine §12.8 requires, so the nine cases below are §12.8
// cases: what they observe is the two §12.8 reports, withheld. CheckBreakScope
// and CheckJumpLeaf in
// src/elaborator/elaborator_validate_jump_statements.cpp emit them, and
// JumpScope::in_production_code_block is the term that withholds them.
//
// A.6.12 reaches an rs_code_block from two places in an rs_rule -- an rs_prod
// may be one, whose statements the parser keeps in RsProd::code_stmts, and a
// weight_specification may be followed by one, whose statements go in
// RsRule::weight_code -- so each gets a case of its own.

// §18.17.6's own example: the break in the SETUP production's code block has
// no enclosing loop, and the clause makes it leave the randsequence block
// rather than break a loop, so §12.8's "break statement is not inside a loop"
// is not the rule that governs it.
TEST(JumpStatementElaboration, BreakInARandsequenceProductionCodeBlockOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int fifo_length;\n"
      "  int max_length;\n"
      "  initial begin\n"
      "    randsequence()\n"
      "      WRITE : SETUP DATA;\n"
      "      SETUP : { if (fifo_length >= max_length) break; } COMMAND;\n"
      "      DATA : { ; };\n"
      "      COMMAND : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The second rs_code_block A.6.12's rs_rule admits, after the weight. It is a
// separate statement list under Stmt::rs_productions, so the case above does
// not answer for it: the production `a` below has an empty code block, which
// leaves the weight block as the only place the break can stand.
TEST(JumpStatementElaboration, BreakInARandsequenceWeightCodeBlockOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int fifo_length;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := 5 { if (fifo_length > 0) break; };\n"
      "      a : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §18.17.6: a return in a production code block "aborts the generation of the
// current production", which is a meaning it has with no subroutine in sight,
// so §12.8's "return statement is only allowed inside a subroutine" is not the
// rule that governs it. The randsequence here stands in an initial block.
TEST(JumpStatementElaboration,
     ReturnInARandsequenceProductionCodeBlockOutsideASubroutineOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int fifo_length;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { if (fifo_length > 0) return; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The same return written where a subroutine does enclose it. §18.17.6 still
// makes it abort the production rather than the function, so the acceptance
// here is not the function's doing, and a fix that read the enclosing
// subroutine instead of the production code block would pass this case and
// fail the one above.
TEST(JumpStatementElaboration,
     ReturnInARandsequenceProductionCodeBlockInAVoidFunctionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    randsequence(main)\n"
      "      main : { return; };\n"
      "    endsequence\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.8 says of a value-returning function that "the return statement shall
// have an expression of the correct type", and CheckValueReturningFuncReturn
// in src/elaborator/elaborator_validate_jump_statements.cpp reports the bare
// return that breaks it. §18.17.6 makes the bare return below abort the
// production rather than the function, so it is not the function's return and
// that report is not about it. This is the case that pins the one exclusion
// CheckValueReturningFuncReturn makes: it takes its child links from
// ForEachChildStmt and stops at a randsequence statement, whose
// Stmt::rs_productions ForEachChildStmt would otherwise descend.
TEST(JumpStatementElaboration,
     ReturnInARandsequenceProductionCodeBlockInAValueReturningFunctionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f();\n"
      "    randsequence(main)\n"
      "      main : { return; };\n"
      "    endsequence\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §18.17.6 names break and return and says nothing about continue, so a
// continue in a production code block keeps the §12.8 rule that it "can only
// be used in a loop", which CheckContinueScope in
// src/elaborator/elaborator_validate_jump_statements.cpp enforces with no
// §18.17.6 term of its own. Without this case, an implementation that exempted
// every jump statement written inside a randsequence would pass all the cases
// above.
TEST(JumpStatementElaboration,
     ContinueInARandsequenceProductionCodeBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int fifo_length;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { if (fifo_length > 0) continue; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "continue statement is not inside a loop", 5,
                            "12.8"));
}

// §18.17.6's third sentence: "Use of the break statement within a loop
// statement behaves as defined in 12.8. Thus, the break statement terminates
// the smallest enclosing looping statement". The for loop here is written
// inside the production code block, so the break binds to it, and the
// enclosing-loop count has to survive the production term being set rather
// than be replaced by it.
TEST(JumpStatementElaboration,
     BreakInAForLoopInARandsequenceProductionCodeBlockOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { for (int i = 0; i < 4; i++) begin\n"
      "                 if (i == 2) break;\n"
      "               end };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The continue that the case above's break does not answer for: §18.17.6
// leaves continue to §12.8 everywhere, so the loop written inside the
// production code block is what makes this one legal. Paired with
// ContinueInARandsequenceProductionCodeBlockIsError it says that the loop, and
// not the production, is what continue is counted against.
TEST(JumpStatementElaboration,
     ContinueInAForLoopInARandsequenceProductionCodeBlockOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { for (int i = 0; i < 4; i++) begin\n"
      "                 if (i == 2) continue;\n"
      "               end };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A break in a production code block whose only enclosing loop is outside the
// randsequence block. It binds to the randsequence block, not to that loop:
// §18.17.6 states without qualification that "when a break statement is
// executed from within a production code block, it forces a jump out of the
// randsequence block", and its "within a loop statement" sentence is about a
// loop the code block itself writes, which this source does not. So the break
// leaves the randsequence and execution resumes after endsequence, which here
// is the end of the for loop's body and therefore its next iteration. The
// elaborator accepts the source on either reading, one because §18.17.6
// exempts the break and the other because §12.8 finds it a loop; the reading
// is what the randsequence executor has to implement, and this case fixes
// which reading the comment in CheckBreakScope records.
TEST(JumpStatementElaboration,
     BreakInARandsequenceProductionCodeBlockInsideAnOuterLoopOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int fifo_length;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i++) begin\n"
      "      randsequence(main)\n"
      "        main : { if (fifo_length > 0) break; };\n"
      "      endsequence\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The cases below stand on Stmt::body of a statement that is not a loop.
// src/parser/parser_stmt.cpp fills that field for StmtKind::kDelay,
// StmtKind::kCycleDelay, StmtKind::kEventControl and StmtKind::kWait as well
// as for the loop statements, and CheckJumpRulesChildren in
// src/elaborator/elaborator_validate_jump_statements.cpp reaches it through
// ForEachChildStmt. §12.8 says "the continue and break statements can only be
// used in a loop" and "the return statement can only be used in a subroutine"
// without qualifying either by what a statement is waiting for, so a jump
// written after a delay, a cycle delay, an event control or a wait is judged
// exactly as one written on its own.

// §12.8: the break is the whole body of a delay control, and no loop encloses
// the delay control, so the break is not inside a loop.
TEST(JumpStatementElaboration, BreakAfterADelayControlIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial #5 break;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "break statement is not inside a loop", 2, "12.8"));
}

// The continue that the case above's break does not answer for. §12.8 holds
// both statements to the same enclosing loop, and CheckContinueScope in
// src/elaborator/elaborator_validate_jump_statements.cpp is a separate
// emission site from CheckBreakScope, so the link carries two reports and not
// one.
TEST(JumpStatementElaboration, ContinueAfterADelayControlIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial #5 continue;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "continue statement is not inside a loop", 2,
                            "12.8"));
}

// §9.4.2's event control fills the same Stmt::body, so §12.8's rule reaches a
// break written after @(posedge clk) as it reaches one written after a delay.
TEST(JumpStatementElaboration, BreakAfterAnEventControlIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  initial @(posedge clk) break;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "break statement is not inside a loop", 3, "12.8"));
}

// §9.4.3's wait statement fills the same Stmt::body. A wait is not a loop, so
// the break it guards is a break outside a loop.
TEST(JumpStatementElaboration, BreakAfterAWaitStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic done;\n"
      "  initial wait (done) break;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "break statement is not inside a loop", 3, "12.8"));
}

// §14.11's cycle delay fills the same Stmt::body. The default clocking is
// there because §14.11 makes a ## without one an error of its own, which would
// leave the source rejected whether §12.8 reported the break or not.
TEST(JumpStatementElaboration, BreakAfterACycleDelayIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial ##1 break;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "break statement is not inside a loop", 5, "12.8"));
}

// The third §12.8 report through the same link: "the return statement can only
// be used in a subroutine", and an initial block is not one. CheckJumpLeaf in
// src/elaborator/elaborator_validate_jump_statements.cpp emits it, reading
// JumpScope::in_subroutine, which an event control neither sets nor clears.
TEST(JumpStatementElaboration,
     ReturnAfterAnEventControlOutsideASubroutineIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  initial @(posedge clk) return;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "return statement is only allowed inside a subroutine", 3, "12.8"));
}

// The enclosing loop count passes through a delay control unchanged. Without
// this case, a walk that reached Stmt::body with a fresh JumpScope rather than
// the caller's would pass every rejection case above.
TEST(JumpStatementElaboration, BreakAfterADelayControlInsideAForLoopOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i++) #5 break;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The enclosing fork-join count passes through a delay control too, which is
// what selects §12.8's second break report rather than its first: "the
// continue and break statements cannot be used inside a fork-join block to
// control a loop outside the fork-join block". The for loop stands outside the
// fork.
TEST(JumpStatementElaboration,
     BreakAfterADelayControlInsideAForkInsideALoopIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i++) begin\n"
      "      fork\n"
      "        #5 break;\n"
      "      join\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "break inside fork-join cannot exit a loop outside "
                            "the fork-join block",
                            5, "12.8"));
}

// §18.17.6's term passes through a delay control as well, so a return written
// after a delay inside a production code block still aborts the production
// rather than a subroutine and §12.8's subroutine rule is still not the one
// that governs it.
TEST(JumpStatementElaboration,
     ReturnAfterADelayControlInARandsequenceProductionCodeBlockOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { #5 return; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The weight code block A.6.12's rs_rule admits after a weight_specification
// is a second statement list under Stmt::rs_productions, and
// CheckValueReturningFuncReturn stops at the randsequence statement, so it
// excludes that list along with the production code blocks. §18.17.6 makes the
// bare return below abort the production rather than the function, so §13.4.1's
// "when the return statement is used, nonvoid functions shall specify an
// expression with the return" is not about it. The production `a` has an empty
// code block, which leaves the weight block as the only place the return can
// stand.
TEST(JumpStatementElaboration,
     ReturnInARandsequenceWeightCodeBlockInAValueReturningFunctionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f();\n"
      "    randsequence(main)\n"
      "      main : a := 5 { return; };\n"
      "      a : { ; };\n"
      "    endsequence\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
