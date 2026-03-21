#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ScopeAndLifetimeSimulation, ExplicitStaticInAutoFuncBlockPersists) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function automatic int get_id();\n"
      "    begin\n"
      "      static int next_id = 0;\n"
      "      next_id = next_id + 1;\n"
      "      return next_id;\n"
      "    end\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = get_id();\n"
      "    result = get_id();\n"
      "    result = get_id();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

TEST(ScopeAndLifetimeSimulation, ExplicitAutoInStaticFuncBlockFresh) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function static int get_val();\n"
      "    begin\n"
      "      automatic int temp = 10;\n"
      "      temp = temp + 1;\n"
      "      return temp;\n"
      "    end\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = get_val();\n"
      "    result = get_val();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 11u);
}

TEST(ScopeAndLifetimeSimulation, ForLoopVariableCountsCorrectly) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    for (int i = 0; i < 5; i = i + 1) begin\n"
      "      result = result + i;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 10u);
}

TEST(ScopeAndLifetimeSimulation, NestedForLoopVarsScopedCorrectly) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    for (int i = 0; i < 3; i = i + 1) begin\n"
      "      for (int j = 0; j < 2; j = j + 1) begin\n"
      "        result = result + 1;\n"
      "      end\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 6u);
}

}  // namespace
