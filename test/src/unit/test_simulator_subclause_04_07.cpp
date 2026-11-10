#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <sstream>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::vector<std::string> SortedLines(const std::string& text) {
  std::vector<std::string> lines;
  std::istringstream in(text);
  std::string line;
  while (std::getline(in, line)) lines.push_back(line);
  std::sort(lines.begin(), lines.end());
  return lines;
}

TEST(NondeterminismSim, ActiveProcessesWritingOneVariableLeaveEitherWrite) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial a = 8'd1;\n"
      "  initial a = 8'd2;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  uint64_t value = a->value.ToUint64();
  EXPECT_TRUE(value == 1u || value == 2u) << value;
}

TEST(NondeterminismSim, ReactiveProcessesWritingOneVariableLeaveEitherWrite) {
  SimFixture f;
  std::string out = RunCapture(
      "module top;\n"
      "  program p;\n"
      "    logic [7:0] a;\n"
      "    initial a = 8'd1;\n"
      "    initial a = 8'd2;\n"
      "    initial #1 $display(\"a=%0d\", a);\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(out == "a=1\n" || out == "a=2\n") << out;
}

TEST(NondeterminismSim, ProcessesInterleaveAtATimeControl) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $display(\"a1\");\n"
      "    #0 $display(\"a2\");\n"
      "  end\n"
      "  initial begin\n"
      "    $display(\"b1\");\n"
      "    #0 $display(\"b2\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_EQ(out.size(), 12u) << out;
  EXPECT_EQ(SortedLines(out.substr(0, 6)),
            (std::vector<std::string>{"a1", "b1"}));
  EXPECT_EQ(SortedLines(out.substr(6)), (std::vector<std::string>{"a2", "b2"}));
}

TEST(NondeterminismSim, ReadModifyWritesOfTwoProcessesLeaveOneOrBoth) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  int x = 0;\n"
      "  initial x = x + 1;\n"
      "  initial x = x + 1;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  uint64_t value = x->value.ToUint64();
  EXPECT_TRUE(value == 1u || value == 2u) << value;
}

}  // namespace
