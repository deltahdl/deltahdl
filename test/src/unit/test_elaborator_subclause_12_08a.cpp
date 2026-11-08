#include <gtest/gtest.h>

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
      "    static int i = 0;\n"
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
                            "gives no value to return",
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

TEST(JumpStatementElaboration, ReturnStringLiteralFromNumericFunctionsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int compute();\n"
      "    return \"hello\";\n"
      "  endfunction\n"
      "  function bit [15:0] pair();\n"
      "    return \"hi\";\n"
      "  endfunction\n"
      "  function real scale();\n"
      "    return \"a\";\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnStringLiteralFromClassFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  function A g();\n"
      "    return \"hello\";\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'g' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            4, "12.8"));
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

TEST(JumpStatementElaboration, BreakAfterACycleDelayIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m; logic clk;\n"
      "  logic data; default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial ##1 break;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "break statement is not inside a loop", 5, "12.8"));
}

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

TEST(JumpStatementElaboration, BreakOutsideALoopInAClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  task go;\n"
      "    break;\n"
      "  endtask\n"
      "endclass\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "break statement is not inside a loop", 3, "12.8"));
}

TEST(JumpStatementElaboration, BareReturnInAConstructorIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  function new();\n"
      "    return;\n"
      "  endfunction\n"
      "endclass\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
