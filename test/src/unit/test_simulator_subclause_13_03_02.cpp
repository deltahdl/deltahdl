#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §13.3.2: variables declared in a static task shall be initialized to the
// default initialization value and retain their values between invocations.
// First call observes the default (x starts at 0, so v == 5); the second call
// observes retention (x kept its 5, so v == 10).
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

// §13.3.2: the arguments of a static task -- including output arguments -- are
// static storage that retains its value between invocations. An output argument
// is never passed a value from the caller, so a read-before-write on the second
// call observes the value left behind by the first. The task increments its own
// output before copying it back, so retention yields 1 then 2; if the output
// were (wrongly) re-defaulted each call, both calls would produce 1.
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

// §13.3.2 + §13.5.1: an output argument of an automatic task is not passed the
// caller's value; it is replicated and reinitialized to the default value
// whenever execution enters its scope. Using a 2-state type (default 0), each
// call computes 0 + 1 = 1 and copies it out, so the result is 1 regardless of
// how many times the task ran before. (If the output were wrongly seeded from
// the caller, the second call would read the retained 1 and produce 2.)
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

// §13.3.2: a local variable of an automatic task is reallocated and default
// initialized on every entry, so its value never carries across invocations.
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

// §13.3.2: input arguments of an automatic task shall be initialized to the
// values passed from the corresponding expressions in the enabling statement.
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

// §13.3.2: inout arguments are initialized to the passed value on entry and the
// final value is copied back out, so the round trip observes both directions.
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

// §13.3.2: a static task's storage belongs to its module instance, so separate
// instances of the same module have independent storage. Each instance calls
// the task twice; with separate storage both counters reach 2, whereas shared
// storage would let one instance's calls bleed into the other's count.
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

// §13.3.2: a task may be enabled more than once concurrently; every variable of
// an automatic task is replicated per concurrent invocation so each activation
// keeps its own state. Two branches of a fork enter the same automatic task and
// each stashes its own seed into the task local before the shared delay; after
// the delay each reads back its own copy. Separate storage yields 11 and 22;
// shared storage would let the second activation's write clobber the first.
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

// §13.3.2: all variables of a static task are static -- a single variable per
// declared local in the module instance, regardless of how many activations are
// concurrent. The same fork enters a static task twice; both activations share
// the one storage cell, so the second activation's write is what both read back
// after the delay. Shared storage yields 22 and 22; per-invocation storage
// would (wrongly) preserve the first activation's 11.
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

}  // namespace
