#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §13.3.2: Static task variables retain values between invocations.
TEST(Sim13032, StaticTaskRetainsValues) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task static accum(input logic [31:0] v, output logic [31:0] out);\n"
      "    int sum;\n"
      "    sum = sum + v;\n"
      "    out = sum;\n"
      "  endtask\n"
      "  initial begin\n"
      "    accum(32'd10, result);\n"
      "    accum(32'd20, result);\n"
      "    accum(32'd30, result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  // sum persists: 10 → 30 → 60
  EXPECT_EQ(val, 60u);
}

// §13.3.2: Automatic task variables are fresh each invocation.
TEST(Sim13032, AutomaticTaskFreshVars) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task automatic accum(input logic [31:0] v, output logic [31:0] out);\n"
      "    int sum;\n"
      "    sum = sum + v;\n"
      "    out = sum;\n"
      "  endtask\n"
      "  initial begin\n"
      "    accum(32'd10, result);\n"
      "    accum(32'd20, result);\n"
      "    accum(32'd30, result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  // sum starts at 0 each call (automatic): 0+30 = 30
  EXPECT_EQ(val, 30u);
}

// §13.3.2: Static task input/output/inout args also retain values.
TEST(Sim13032, StaticTaskArgsRetainValues) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task static bump(inout logic [31:0] v);\n"
      "    v = v + 1;\n"
      "  endtask\n"
      "  initial begin\n"
      "    result = 32'd0;\n"
      "    bump(result);\n"
      "    bump(result);\n"
      "    bump(result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

// §13.3.2: Automatic task output args initialized from caller.
TEST(Sim13032, AutomaticTaskInputFromCaller) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task automatic compute(input logic [31:0] a, input logic [31:0] b,\n"
      "                         output logic [31:0] out);\n"
      "    out = a + b;\n"
      "  endtask\n"
      "  initial begin\n"
      "    compute(32'd15, 32'd27, result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 42u);
}

}  // namespace
