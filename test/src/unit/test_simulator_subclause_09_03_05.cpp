#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(StatementLabelSimulation, LabeledStatementExecutes) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    step1: x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

TEST(StatementLabelSimulation, LabeledBeginBlockExecutes) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    blk: begin\n"
      "      result = 99;\n"
      "    end : blk\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 99u);
}

TEST(StatementLabelSimulation, LabeledForLoopExecutes) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    sum: for (int i = 0; i < 5; i = i + 1)\n"
      "      result = result + 1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 5u);
}

TEST(StatementLabelSimulation, LabeledIfElseExecutes) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    pick: if (0) result = 1; else result = 2;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 2u);
}

TEST(StatementLabelSimulation, LabeledCaseExecutes) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    decode: case (2)\n"
      "      0: result = 10;\n"
      "      1: result = 20;\n"
      "      2: result = 30;\n"
      "      default: result = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 30u);
}

TEST(StatementLabelSimulation, LabeledWhileExecutes) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    cnt: while (result < 4) result = result + 1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 4u);
}

TEST(StatementLabelSimulation, LabeledDoWhileExecutes) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    bump: do result = result + 1; while (result < 3);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

TEST(StatementLabelSimulation, LabeledRepeatExecutes) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    pulse: repeat (5) result = result + 1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 5u);
}

TEST(StatementLabelSimulation, LabeledNonblockingAssignExecutes) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    drive: result <= 8'd77;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 77u);
}

TEST(StatementLabelSimulation, MultipleLabelsInSequenceExecute) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    s1: result = 1;\n"
      "    s2: result = result + 10;\n"
      "    s3: result = result + 100;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 111u);
}

TEST(StatementLabelSimulation, LabeledBeginBlockWithLocalVar) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    work: begin\n"
      "      int tmp;\n"
      "      tmp = 7;\n"
      "      result = tmp * 3;\n"
      "    end : work\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 21u);
}

// §9.3.5 — a statement label on a for loop that declares its loop variable
// names the implicit block the loop creates (weave 12.7.3), and a labeled
// statement can be disabled with the same behavior as disabling a named block
// (weave 9.6.2). Disabling the loop by its own label therefore terminates the
// whole loop — acting like a break — and execution resumes at the statement
// following it.
TEST(StatementLabelSimulation, DisableLabeledForLoopActsLikeBreak) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] count, after;\n"
      "  initial begin\n"
      "    count = 8'd0;\n"
      "    after = 8'd0;\n"
      "    run: for (int i = 0; i < 8; i = i + 1) begin\n"
      "      if (i == 3) disable run;\n"
      "      count = count + 8'd1;\n"
      "    end\n"
      "    after = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  // count reaches 3 (iterations i=0,1,2), then i=3 disables the loop before the
  // increment; `after` proves execution resumed past the loop.
  LowerRunAndCheck(f, design, {{"count", 3u}, {"after", 1u}});
}

// §9.3.5 — the same rule for a foreach loop: its label names the loop's
// implicit block, so disabling that label ends the entire foreach and resumes
// after it.
TEST(StatementLabelSimulation, DisableLabeledForeachActsLikeBreak) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [8];\n"
      "  logic [7:0] visited, after;\n"
      "  initial begin\n"
      "    visited = 8'd0;\n"
      "    after = 8'd0;\n"
      "    scan: foreach (arr[i]) begin\n"
      "      if (i == 3) disable scan;\n"
      "      visited = visited + 8'd1;\n"
      "    end\n"
      "    after = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"visited", 3u}, {"after", 1u}});
}

// §9.3.5 — a begin-end block is a statement, so a label before begin is
// equivalent to a block name after it, and a labeled statement disables with
// the same behavior as a named block (weave 9.6.2). Disabling the block by its
// prefix label from inside terminates it, skipping the block's remaining
// statements, and control resumes at the statement following the block. This
// exercises the labeled begin-end disable path, distinct from the loop path.
TEST(StatementLabelSimulation, DisableLabeledBeginBlockByPrefixLabel) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] got_here, not_reached, after;\n"
      "  initial begin\n"
      "    got_here = 8'd0;\n"
      "    not_reached = 8'd0;\n"
      "    after = 8'd0;\n"
      "    blk: begin\n"
      "      got_here = 8'd1;\n"
      "      disable blk;\n"
      "      not_reached = 8'd1;\n"
      "    end\n"
      "    after = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  // The block runs up to the disable, then ends; not_reached stays 0 and after
  // proves execution continued past the disabled block.
  LowerRunAndCheck(f, design,
                   {{"got_here", 1u}, {"not_reached", 0u}, {"after", 1u}});
}

TEST(StatementLabelSimulation, LabeledForkJoinExecutes) {
  // Labeling a fork-join block creates its named scope without disturbing
  // execution: the parent blocks on join and the spawned assignment lands.
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    work: fork\n"
      "      result = 55;\n"
      "    join : work\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 55u);
}

}  // namespace
