#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ProceduralAssignSim, AssignInCalledTask) {
  auto result = RunAndGet(
      "module t;\n"
      "  int x;\n"
      "  task do_set();\n"
      "    x = 55;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    do_set();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 55u);
}

TEST(ProceduralAssignSim, AssignInCalledFunction) {
  auto result = RunAndGet(
      "module t;\n"
      "  function int double_it(int v);\n"
      "    int tmp;\n"
      "    tmp = v * 2;\n"
      "    return tmp;\n"
      "  endfunction\n"
      "  int y;\n"
      "  initial begin\n"
      "    y = double_it(21);\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(result, 42u);
}

}  // namespace
