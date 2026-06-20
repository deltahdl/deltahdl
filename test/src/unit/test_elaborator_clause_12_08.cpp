#include "fixture_elaborator.h"

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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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

TEST(JumpStatementElaboration, BreakInsideMultiDimForeachOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int matrix[2][3];\n"
      "  initial begin\n"
      "    foreach (matrix[i, j]) begin\n"
      "      if (matrix[i][j] == 0) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ContinueInsideMultiDimForeachOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int matrix[2][3];\n"
      "  initial begin\n"
      "    foreach (matrix[i, j]) begin\n"
      "      if (matrix[i][j] == 0) continue;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
