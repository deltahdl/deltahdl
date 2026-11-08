#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ScopeRandomizeWith, InlineConstraintConstrainsNamedArgument) {
  const char* src =
      "module top;\n"
      "  int okv;\n"
      "  int aval;\n"
      "  initial begin\n"
      "    bit [7:0] a;\n"
      "    okv = std::randomize(a) with { a == 200; };\n"
      "    aval = a;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "aval"), 200u);
}

TEST(ScopeRandomizeWith, NonArgumentIsStateVariableReadAsConstant) {
  const char* src =
      "module top;\n"
      "  int okv;\n"
      "  int aval;\n"
      "  task run(int length);\n"
      "    bit [7:0] a;\n"
      "    okv = std::randomize(a) with { a > length; };\n"
      "    aval = a;\n"
      "  endtask\n"
      "  initial run(100);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_GT(RunAndGet(src, "aval"), 100u);
}

TEST(ScopeRandomizeWith, StateVariableValueGovernsEachDraw) {
  const char* src =
      "module top;\n"
      "  int a_lo;\n"
      "  int a_hi;\n"
      "  initial begin\n"
      "    bit [7:0] a;\n"
      "    int length;\n"
      "    int s1, s2;\n"
      "    length = 50;\n"
      "    s1 = std::randomize(a) with { a > length; };\n"
      "    a_lo = a;\n"
      "    length = 200;\n"
      "    s2 = std::randomize(a) with { a > length; };\n"
      "    a_hi = a;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "a_lo"), 50u);
  EXPECT_GT(RunAndGet(src, "a_hi"), 200u);
}

TEST(ScopeRandomizeWith, NonArgumentLocalKeepsItsValue) {
  const char* src =
      "module top;\n"
      "  int okv;\n"
      "  int aval;\n"
      "  int bval;\n"
      "  initial begin\n"
      "    bit [7:0] a;\n"
      "    bit [7:0] b;\n"
      "    b = 8'd77;\n"
      "    okv = std::randomize(a) with { a == 30; };\n"
      "    aval = a;\n"
      "    bval = b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "aval"), 30u);
  EXPECT_EQ(RunAndGet(src, "bval"), 77u);
}

TEST(ScopeRandomizeWith, JointConstraintOverArgumentsAgainstStateValue) {
  const char* src =
      "module top;\n"
      "  int okv;\n"
      "  int sumv;\n"
      "  task run(int length);\n"
      "    bit [3:0] a;\n"
      "    bit [3:0] b;\n"
      "    okv = std::randomize(a, b) with { a + b < length; };\n"
      "    sumv = a + b;\n"
      "  endtask\n"
      "  initial run(10);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_LT(RunAndGet(src, "sumv"), 10u);
}

TEST(ScopeRandomizeWith, NamedArgumentWithoutConstraintIsStillRandomized) {
  const char* src =
      "module top;\n"
      "  int okv;\n"
      "  int aval;\n"
      "  int unk_c;\n"
      "  initial begin\n"
      "    logic [7:0] a;\n"
      "    logic [7:0] c;\n"
      "    okv = std::randomize(a, c) with { a == 5; };\n"
      "    aval = a;\n"
      "    unk_c = $isunknown(c);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "aval"), 5u);
  EXPECT_EQ(RunAndGet(src, "unk_c"), 0u);
}

TEST(ScopeRandomizeWith, UnsatisfiableAgainstStateValueFails) {
  const char* src =
      "module top;\n"
      "  int okv;\n"
      "  int aval;\n"
      "  int bval;\n"
      "  task run(int length);\n"
      "    bit [3:0] a;\n"
      "    bit [3:0] b;\n"
      "    a = 4'd9;\n"
      "    b = 4'd8;\n"
      "    okv = std::randomize(a, b) with { a + b > length; };\n"
      "    aval = a;\n"
      "    bval = b;\n"
      "  endtask\n"
      "  initial run(100);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 0u);
  EXPECT_EQ(RunAndGet(src, "aval"), 9u);
  EXPECT_EQ(RunAndGet(src, "bval"), 8u);
}

TEST(ScopeRandomizeWith, IntArgumentsRandomizedAgainstStateValue) {
  const char* src =
      "module top;\n"
      "  int okv;\n"
      "  int sumv;\n"
      "  task run(int length);\n"
      "    int a;\n"
      "    int b;\n"
      "    okv = std::randomize(a, b) with { a < 5; b < 5; a + b < length; };\n"
      "    sumv = a + b;\n"
      "  endtask\n"
      "  initial run(6);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_LT(static_cast<int32_t>(RunAndGet(src, "sumv")), 6);
}

TEST(ScopeRandomizeWith, ParameterServesAsStateConstant) {
  const char* src =
      "module top;\n"
      "  parameter int LIMIT = 100;\n"
      "  int okv;\n"
      "  int aval;\n"
      "  initial begin\n"
      "    bit [7:0] a;\n"
      "    okv = std::randomize(a) with { a > LIMIT; };\n"
      "    aval = a;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_GT(RunAndGet(src, "aval"), 100u);
}

TEST(ScopeRandomizeWith, LocalparamServesAsStateConstant) {
  const char* src =
      "module top;\n"
      "  localparam int FLOOR = 200;\n"
      "  int okv;\n"
      "  int aval;\n"
      "  initial begin\n"
      "    bit [7:0] a;\n"
      "    okv = std::randomize(a) with { a > FLOOR; };\n"
      "    aval = a;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_GT(RunAndGet(src, "aval"), 200u);
}

TEST(ScopeRandomizeWith, WithFormInsideFunctionScope) {
  const char* src =
      "module top;\n"
      "  int okv;\n"
      "  int aval;\n"
      "  function int rand_it();\n"
      "    bit [7:0] a;\n"
      "    int r;\n"
      "    r = std::randomize(a) with { a == 88; };\n"
      "    aval = a;\n"
      "    return r;\n"
      "  endfunction\n"
      "  initial okv = rand_it();\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "aval"), 88u);
}

}  // namespace
