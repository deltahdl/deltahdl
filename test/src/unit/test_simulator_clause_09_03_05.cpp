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

}  // namespace
