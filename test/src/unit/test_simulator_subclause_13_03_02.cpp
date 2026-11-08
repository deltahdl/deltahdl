#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(TaskMemorySim, StaticTaskVarDefaultInitThenRetains) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task static accum(output logic [31:0] v);\n"
      "    int x;\n"
      "    x = x + 5;\n"
      "    v = x;\n"
      "  endtask\n"
      "  initial begin\n"
      "    accum(result);\n"
      "    accum(result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 10u);
}

TEST(TaskMemorySim, StaticTaskOutputArgRetainsBetweenInvocations) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task static acc(output int v);\n"
      "    v = v + 1;\n"
      "  endtask\n"
      "  initial begin\n"
      "    acc(result);\n"
      "    acc(result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 2u);
}

TEST(TaskMemorySim, AutomaticTaskOutputArgDefaultInitEachEntry) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task automatic bump(output int v);\n"
      "    v = v + 1;\n"
      "  endtask\n"
      "  initial begin\n"
      "    bump(result);\n"
      "    bump(result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 1u);
}

TEST(TaskMemorySim, AutomaticTaskLocalReinitializedEachEntry) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task automatic step(output logic [31:0] v);\n"
      "    int x;\n"
      "    x = x + 1;\n"
      "    v = x;\n"
      "  endtask\n"
      "  initial begin\n"
      "    step(result);\n"
      "    step(result);\n"
      "    step(result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 1u);
}

TEST(TaskMemorySim, AutomaticTaskInputArgFromCallExpression) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task automatic dbl(input int a, output logic [31:0] v);\n"
      "    v = a * 2;\n"
      "  endtask\n"
      "  initial begin\n"
      "    dbl(3 + 4, result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 14u);
}

TEST(TaskMemorySim, AutomaticTaskInoutArgRoundTrip) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  task automatic inc(inout logic [31:0] c);\n"
      "    c = c + 1;\n"
      "  endtask\n"
      "  initial begin\n"
      "    result = 41;\n"
      "    inc(result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 42u);
}

TEST(TaskMemorySim, StaticTaskStorageIsPerInstance) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module sub;\n"
      "  logic [31:0] r;\n"
      "  task static bump(output logic [31:0] v);\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    v = cnt;\n"
      "  endtask\n"
      "  initial begin\n"
      "    bump(r);\n"
      "    bump(r);\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  sub a();\n"
      "  sub b();\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a.r", 2u}, {"b.r", 2u}});
}

TEST(TaskMemorySim, AutomaticTaskConcurrentInvocationsHaveSeparateStorage) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] r1, r2;\n"
      "  task automatic tk(input int seed, output logic [31:0] o);\n"
      "    int x;\n"
      "    x = seed;\n"
      "    #10;\n"
      "    o = x;\n"
      "  endtask\n"
      "  initial fork\n"
      "    tk(11, r1);\n"
      "    tk(22, r2);\n"
      "  join\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 11u}, {"r2", 22u}});
}

TEST(TaskMemorySim, StaticTaskConcurrentInvocationsShareStorage) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] r1, r2;\n"
      "  task static tk(input int seed, output logic [31:0] o);\n"
      "    int x;\n"
      "    x = seed;\n"
      "    #10;\n"
      "    o = x;\n"
      "  endtask\n"
      "  initial fork\n"
      "    tk(11, r1);\n"
      "    tk(22, r2);\n"
      "  join\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 22u}, {"r2", 22u}});
}

TEST(TaskMemorySim, StaticTaskOutputQueueFormalRetainsValue) {
  auto val = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  task add(output int o[$], input int v);\n"
      "    o.push_back(v);\n"
      "  endtask\n"
      "  initial begin\n"
      "    add(q, 3);\n"
      "    add(q, 4);\n"
      "    result = q.size() * 100 + q[0] * 10 + q[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 234u);
}

TEST(TaskMemorySim, StaticFunctionOutputFixedFormalRetainsValue) {
  auto val = RunAndGet(
      "module t;\n"
      "  int f[2];\n"
      "  int result;\n"
      "  function void acc(output int a[2], input int v);\n"
      "    a[0] = a[0] + v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    acc(f, 2);\n"
      "    acc(f, 3);\n"
      "    result = f[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 5u);
}

TEST(TaskMemorySim, StaticTaskQueueLocalRetainsValue) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  task grow(output int n);\n"
      "    int q[$];\n"
      "    q.push_back(7);\n"
      "    n = q.size();\n"
      "  endtask\n"
      "  initial begin\n"
      "    grow(result);\n"
      "    grow(result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 2u);
}

}  // namespace
