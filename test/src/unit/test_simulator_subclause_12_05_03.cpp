#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

std::string ExactlyOnceSrc(const char* qualifier, const char* sel_ret) {
  return std::string(
             "module t;\n"
             "  int cnt;\n"
             "  logic [7:0] x;\n"
             "  function automatic logic [7:0] sel_fn();\n"
             "    cnt = cnt + 1;\n"
             "    return ") +
         sel_ret +
         ";\n"
         "  endfunction\n"
         "  initial begin\n"
         "    cnt = 0;\n"
         "    x = 8'd0;\n"
         "    " +
         qualifier +
         " case (sel_fn())\n"
         "      8'd1: x = 8'd11;\n"
         "      8'd2: x = 8'd22;\n"
         "      8'd3: x = 8'd33;\n"
         "    endcase\n"
         "  end\n"
         "endmodule\n";
}

TEST(CaseQualifierSim, UniqueCaseExpressionEvaluatedExactlyOnce) {
  SimFixture f;
  EXPECT_EQ(RunModule(f, ExactlyOnceSrc("unique", "8'd1").c_str(), "cnt"), 1u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 11u);
}

TEST(CaseQualifierSim, UniqueCaseExprEvaluatedBeforeItemExpr) {
  SimFixture f;
  auto [case_seq, item_seq] = RunModuleTwoVars(
      f,
      "module t;\n"
      "  int seq, case_seq, item_seq;\n"
      "  logic [7:0] x;\n"
      "  function automatic logic [7:0] sel_fn();\n"
      "    seq = seq + 1;\n"
      "    case_seq = seq;\n"
      "    return 8'd1;\n"
      "  endfunction\n"
      "  function automatic logic [7:0] pat_fn(input logic [7:0] v);\n"
      "    seq = seq + 1;\n"
      "    item_seq = seq;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    seq = 0; case_seq = 0; item_seq = 0;\n"
      "    x = 8'd0;\n"
      "    unique case (sel_fn())\n"
      "      pat_fn(8'd1): x = 8'd11;\n"
      "      default: x = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      "case_seq", "item_seq");
  EXPECT_EQ(case_seq, 1u);
  EXPECT_GT(item_seq, case_seq);
}

TEST(CaseQualifierSim, Unique0CaseExpressionEvaluatedExactlyOnce) {
  SimFixture f;
  EXPECT_EQ(RunModule(f, ExactlyOnceSrc("unique0", "8'd2").c_str(), "cnt"), 1u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 22u);
}

TEST(CaseQualifierSim, Unique0OverlapRunsOnlyFirstMatch) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    x = 8'd0;\n"
                      "    unique0 case (8'd1)\n"
                      "      8'd1: x = 8'd11;\n"
                      "      8'd1: x = 8'd22;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            11u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseQualifierSim, UniqueOverlapRunsOnlyFirstMatch) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    x = 8'd0;\n"
                      "    unique case (8'd1)\n"
                      "      8'd1: x = 8'd11;\n"
                      "      8'd1: x = 8'd22;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            11u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseQualifierSim, PriorityFirstMatchRunsExactlyOneBody) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    x = 8'd0;\n"
                      "    priority casez (8'b00000011)\n"
                      "      8'b000000?1: x = 8'd11;\n"
                      "      8'b0000001?: x = 8'd22;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            11u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(CaseQualifierSim, UniqueSingleItemMultiplePatternsIsNotViolation) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    x = 8'd0;\n"
                      "    unique casez (8'b00000011)\n"
                      "      8'b000000?1, 8'b0000001?: x = 8'd77;\n"
                      "      8'b11111111: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            77u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(CaseQualifierSim, Unique0SingleItemMultiplePatternsIsNotViolation) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    x = 8'd0;\n"
                      "    unique0 casez (8'b00000011)\n"
                      "      8'b000000?1, 8'b0000001?: x = 8'd77;\n"
                      "      8'b11111111: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            77u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(CaseQualifierSim, Unique0NoMatchProducesNoViolation) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    x = 8'd42;\n"
                      "    unique0 case (8'd9)\n"
                      "      8'd0: x = 8'd1;\n"
                      "      8'd1: x = 8'd2;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            42u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(CaseQualifierSim, PriorityNoMatchIssuesViolation) {
  SimFixture f;
  RunModuleNoVar(f,
                 "module t;\n"
                 "  logic [7:0] x;\n"
                 "  initial begin\n"
                 "    x = 8'd0;\n"
                 "    priority case (8'd9)\n"
                 "      8'd0: x = 8'd1;\n"
                 "      8'd1: x = 8'd2;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseQualifierSim, UniqueNoMatchIssuesViolation) {
  SimFixture f;
  RunModuleNoVar(f,
                 "module t;\n"
                 "  logic [7:0] x;\n"
                 "  initial begin\n"
                 "    x = 8'd0;\n"
                 "    unique case (8'd9)\n"
                 "      8'd0: x = 8'd1;\n"
                 "      8'd1: x = 8'd2;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseQualifierSim, UniqueVariableSelectorNoMatchIssuesViolation) {
  SimFixture f;
  RunModuleNoVar(f,
                 "module t;\n"
                 "  bit [2:0] a;\n"
                 "  logic [7:0] x;\n"
                 "  initial begin\n"
                 "    x = 8'd0;\n"
                 "    a = 3'd5;\n"
                 "    unique case (a)\n"
                 "      3'd0, 3'd1: x = 8'd11;\n"
                 "      3'd2: x = 8'd22;\n"
                 "      3'd4: x = 8'd44;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseQualifierSim, UniqueVariableSelectorMatchesMultiExprItem) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  bit [2:0] a;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    x = 8'd0;\n"
                      "    a = 3'd1;\n"
                      "    unique case (a)\n"
                      "      3'd0, 3'd1: x = 8'd11;\n"
                      "      3'd2: x = 8'd22;\n"
                      "      3'd4: x = 8'd44;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            11u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(CaseQualifierSim, UniqueNoMatchWithDefaultSilent) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    x = 8'd0;\n"
                      "    unique case (8'd9)\n"
                      "      8'd0: x = 8'd1;\n"
                      "      8'd1: x = 8'd2;\n"
                      "      default: x = 8'd55;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            55u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
