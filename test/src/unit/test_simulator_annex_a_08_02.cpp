#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(SubroutineCallSim, FunctionCallWithPositionalArgsReturnsValue) {
  EXPECT_EQ(
      RunAndGet("module t;\n"
                "  function int add(int a, int b); return a + b; endfunction\n"
                "  int r;\n"
                "  initial r = add(20, 22);\n"
                "endmodule\n",
                "r"),
      42u);
}

TEST(SubroutineCallSim, NamedArgumentsBindByName) {
  EXPECT_EQ(
      RunAndGet("module t;\n"
                "  function int sub(int a, int b); return a - b; endfunction\n"
                "  int r;\n"
                "  initial r = sub(.b(3), .a(10));\n"
                "endmodule\n",
                "r"),
      7u);
}

TEST(SubroutineCallSim, MixedPositionalAndNamedArguments) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  function int f3(int a, int b, int c);\n"
                      "    return a * 100 + b * 10 + c;\n"
                      "  endfunction\n"
                      "  int r;\n"
                      "  initial r = f3(1, 2, .c(3));\n"
                      "endmodule\n",
                      "r"),
            123u);
}

TEST(SubroutineCallSim, ArrayReductionSumOverInitializedArray) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int arr[] = {10, 20, 30};\n"
                      "  int r;\n"
                      "  initial r = arr.sum();\n"
                      "endmodule\n",
                      "r"),
            60u);
}

TEST(SubroutineCallSim, ArrayReductionAndKeyword) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int arr[] = {7, 6};\n"
                      "  int r;\n"
                      "  initial r = arr.and;\n"
                      "endmodule\n",
                      "r"),
            6u);
}

TEST(SubroutineCallSim, ArrayReductionOrKeyword) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int arr[] = {1, 2};\n"
                      "  int r;\n"
                      "  initial r = arr.or;\n"
                      "endmodule\n",
                      "r"),
            3u);
}

TEST(SubroutineCallSim, ArrayReductionXorKeyword) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int arr[] = {6, 3};\n"
                      "  int r;\n"
                      "  initial r = arr.xor;\n"
                      "endmodule\n",
                      "r"),
            5u);
}

TEST(SubroutineCallSim, ArrayReductionWithClause) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int arr[] = {1, 2, 3, 4};\n"
                      "  int r;\n"
                      "  initial r = arr.sum() with (item * 2);\n"
                      "endmodule\n",
                      "r"),
            20u);
}

TEST(SubroutineCallSim, ASystemCallSizesAndNamesADataType) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  initial $display(\"%0d %0d %s\", $bits(int unsigned),\n"
                 "      $bits(struct packed { bit a; byte b; }),\n"
                 "      $typename(int unsigned));\n"
                 "endmodule\n",
                 f),
      "32 9 int unsigned\n");
}

}  // namespace
