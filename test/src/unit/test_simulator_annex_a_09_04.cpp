#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

// §A.9.4: white_space ::= space | tab | newline | formfeed | eof — observed at
// the simulator stage: each non-EOF alternative must successfully separate
// tokens in a source that simulates to the expected result.

TEST(WhiteSpaceSim, WhitespaceSameResultWithSpaces) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    result = a + b;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 30u);
}

TEST(WhiteSpaceSim, WhitespaceSameResultWithTabs) {
  auto result = RunAndGet(
      "module\tt\t;\n"
      "\tlogic\t[7:0]\ta\t,\tb\t,\tresult\t;\n"
      "\tinitial\tbegin\n"
      "\t\ta\t=\t8'd10\t;\n"
      "\t\tb\t=\t8'd20\t;\n"
      "\t\tresult\t=\ta\t+\tb\t;\n"
      "\tend\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 30u);
}

TEST(WhiteSpaceSim, WhitespaceSameResultWithNewlines) {
  auto result = RunAndGet(
      "module\n"
      "t\n"
      ";\n"
      "logic\n"
      "[7:0]\n"
      "result\n"
      ";\n"
      "initial\n"
      "result\n"
      "=\n"
      "8'd42\n"
      ";\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(WhiteSpaceSim, WhitespaceFormfeedInSource) {
  auto result = RunAndGet(
      "module t;\f"
      "logic [7:0] result;\f"
      "initial result = 8'd99;\f"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 99u);
}

// §A.9.4 eof alternative: source ending immediately at EOF — no trailing
// newline or other whitespace after `endmodule` — must still simulate to the
// expected value.
TEST(WhiteSpaceSim, EndOfFileTerminatesSimulation) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd88;\n"
      "endmodule",
      "result");
  EXPECT_EQ(result, 88u);
}
