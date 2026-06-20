#include <string>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// Builds a module whose case_expression is a side-effecting function `sel_fn`
// (bumping `cnt` and returning `sel_ret`), selected by a `qualifier`-case over
// three literal items. Shared by the unique and unique0 "evaluated exactly
// once" tests, which differ only in the qualifier and the selector return.
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

// §12.5.3 (N4): in unique-case and unique0-case, the case_expression is
// evaluated exactly once before any case_item_expression. We observe this by
// using a side-effecting function as the case_expression and checking that
// its counter is incremented exactly one time over the whole case statement.
TEST(CaseQualifierSim, UniqueCaseExpressionEvaluatedExactlyOnce) {
  SimFixture f;
  EXPECT_EQ(RunModule(f, ExactlyOnceSrc("unique", "8'd1").c_str(), "cnt"), 1u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 11u);
}

// §12.5.3 (N4 ordering): the case_expression is evaluated BEFORE any
// case_item_expression. A side-effecting function in the case_expression and
// another in a case_item record their invocation order via a shared sequence
// counter; the case_expression's stamp must be strictly less than the item's.
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

// §12.5.3 (N4 for unique0): in unique0-case, the case_expression is also
// evaluated exactly once. Mirrors UniqueCaseExpressionEvaluatedExactlyOnce
// but for the unique0 qualifier, which the LRM explicitly groups with unique
// for this rule.
TEST(CaseQualifierSim, Unique0CaseExpressionEvaluatedExactlyOnce) {
  SimFixture f;
  EXPECT_EQ(RunModule(f, ExactlyOnceSrc("unique0", "8'd2").c_str(), "cnt"), 1u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 22u);
}

// §12.5.3 (N6/N7 for unique0): the overlap rule applies to both unique-case
// and unique0-case. With two items matching the case_expression the
// implementation issues a violation report and runs only the first matching
// item's body, even when the qualifier is unique0.
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

// §12.5.3 (N7): on a uniqueness violation the implementation executes the
// statement of the FIRST matching case_item; no other matching item runs.
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

// §12.5.3 (N2): priority-case acts on the first match only. With no overlap
// situation this should run cleanly and only the earliest matching item.
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
}

// §12.5.3 (N9): when a single case_item holds multiple case_item_expressions,
// even if more than one matches the case_expression, this is NOT a uniqueness
// violation. The item runs once with no violation report.
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

// §12.5.3 (N13): unique0 with no matching item shall NOT issue a violation.
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

// §12.5.3 (N10): priority-case with no matching item shall issue a violation.
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

// §12.5.3 (N10): unique-case with no matching item shall issue a violation.
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

// §12.5.3 (N6/N7): a unique-case with a default-only fallback still suppresses
// the no-match violation when execution falls through to default.
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
