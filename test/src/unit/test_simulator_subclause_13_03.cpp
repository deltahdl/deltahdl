#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(TaskCall, SetupReturnsTaskItem) {
  SimFixture f;

  auto* task = f.arena.Create<ModuleItem>();
  task->kind = ModuleItemKind::kTaskDecl;
  task->name = "my_task";
  f.ctx.RegisterFunction("my_task", task);

  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "my_task";

  auto* result = SetupTaskCall(call, f.ctx, f.arena);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->name, "my_task");

  TeardownTaskCall(result, call, f.ctx, f.arena);
}

TEST(TaskCall, SetupReturnsNullForFunction) {
  SimFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "my_func";
  f.ctx.RegisterFunction("my_func", func);

  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "my_func";

  auto* result = SetupTaskCall(call, f.ctx, f.arena);
  EXPECT_EQ(result, nullptr);
}

TEST(TaskCall, SetupReturnsNullForUnknown) {
  SimFixture f;
  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "nonexistent";

  auto* result = SetupTaskCall(call, f.ctx, f.arena);
  EXPECT_EQ(result, nullptr);
}

TEST(TaskSim, TaskCallsTask) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  task inner(input logic [31:0] v);\n"
      "    x = v;\n"
      "  endtask\n"
      "  task outer;\n"
      "    inner(32'd42);\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    outer();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

TEST(TaskSim, TaskEmptyBody) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  task nop;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 32'd1;\n"
      "    nop();\n"
      "    x = x + 32'd1;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 2u);
}

TEST(TaskSim, TaskReturnEarlyExit) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  task maybe_set(input logic [31:0] v);\n"
      "    if (v == 0) return;\n"
      "    x = v;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 32'd1;\n"
      "    maybe_set(32'd0);\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 1u);
}

TEST(TaskSim, StaticTaskArgsRetainValues) {
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

TEST(TaskSim, AutomaticTaskInputFromCaller) {
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

TEST(TaskSim, FormalArgInheritedTypeRoundTripsFullWidth) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] result_a;\n"
      "  logic [7:0] result_b;\n"
      "  task fill(output logic [7:0] a, b);\n"
      "    a = 8'hA5;\n"
      "    b = 8'h5A;\n"
      "  endtask\n"
      "  initial fill(result_a, result_b);\n"
      "endmodule\n",
      "result_b");
  EXPECT_EQ(val, 0x5Au);
}

// §13.2 and §13.3 (printed page 335): a task may contain time-controlling
// statements, and control returns to the enabling process only when the task
// has completed, so the time of the return may differ from the time of the
// call; §8.6 (printed page 183) has an object's task enabled through its
// handle, `d.run();`, as any of its methods is. A class task's delay was run
// without consuming time, the call going to the function interpreter, so the
// read of $time after it gave 0 rather than 50.
TEST(TaskSim, ClassTaskCalledThroughAHandleConsumesItsDelay) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  class drv;\n"
      "    task run();\n"
      "      #50;\n"
      "      x = $time;\n"
      "    endtask\n"
      "  endclass\n"
      "  initial begin\n"
      "    drv d = new;\n"
      "    x = 0;\n"
      "    d.run();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 50u);
}

// §13.3: control comes back to the enabling process after the task's delay,
// so the statement after the call runs at the time the task ended.
TEST(TaskSim, ClassTaskCalledThroughAHandleReturnsAfterItsDelay) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] y;\n"
      "  class drv;\n"
      "    task run();\n"
      "      #70;\n"
      "    endtask\n"
      "  endclass\n"
      "  initial begin\n"
      "    drv d = new;\n"
      "    d.run();\n"
      "    y = $time;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 70u);
}

// §13.3 with §9.4.2: an event control inside the class task suspends the
// enabling process until the edge, here the posedge another process drives
// at time 30.
TEST(TaskSim, ClassTaskCalledThroughAHandleWaitsForAnEdge) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  logic clk;\n"
      "  class drv;\n"
      "    task run();\n"
      "      @(posedge clk);\n"
      "      x = $time;\n"
      "    endtask\n"
      "  endclass\n"
      "  initial begin\n"
      "    drv d = new;\n"
      "    x = 0;\n"
      "    d.run();\n"
      "  end\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    #30 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 30u);
}

// §13.3: a class task's input argument binds for the body, and a property of
// the object the handle refers to is written by it (§8.6), after the delay.
TEST(TaskSim, ClassTaskCalledThroughAHandleBindsItsArgumentAndThis) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  class drv;\n"
      "    int count;\n"
      "    task run(input int n);\n"
      "      #10;\n"
      "      count = n + 1;\n"
      "    endtask\n"
      "  endclass\n"
      "  initial begin\n"
      "    drv d = new;\n"
      "    x = 0;\n"
      "    d.run(41);\n"
      "    x = d.count;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

// §13.3 with §8.11: two activations of one class task on two objects, each
// suspended on its delay while the other runs, each write their own object's
// property when they resume -- the object a task runs on travels with the
// process, parked while it is suspended as its locals are, so the activation
// resuming first does not write through the other's `this`.
TEST(TaskSim, TwoSuspendedClassTasksEachWriteTheirOwnObject) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  class drv;\n"
      "    int id, count;\n"
      "    task run();\n"
      "      #(10 * id);\n"
      "      count = id * 100 + $time;\n"
      "    endtask\n"
      "  endclass\n"
      "  initial begin\n"
      "    drv a = new;\n"
      "    drv b = new;\n"
      "    a.id = 1;\n"
      "    b.id = 2;\n"
      "    fork\n"
      "      a.run();\n"
      "      b.run();\n"
      "    join\n"
      "    x = a.count * 1000 + b.count;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 110220u);
}

// §13.3 (printed page 335): a task enabled as a statement runs to completion,
// its timing controls consuming time, before the enabling process goes on;
// §26.3 (printed page 808) references a package's declaration through the
// package scope resolution operator. A package task enabled as `p::pause(9)`
// was dropped whole, so the time read after it was the 6 of the imported
// enable alone rather than 15.
TEST(TaskSim, PackageTaskEnabledThroughItsScopedNameConsumesItsDelay) {
  auto val = RunAndGet(
      "package p;\n"
      "  task pause(int d);\n"
      "    #d;\n"
      "  endtask\n"
      "endpackage\n"
      "module t;\n"
      "  import p::*;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    pause(6);\n"
      "    p::pause(9);\n"
      "    x = $time;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 15u);
}

// §13.3 (printed page 335) enables a task from a statement, and §23.6
// (printed page 753) names an item of another module instance by its
// hierarchical path, so `u1.tk(4)` enables sub's task in the instance u1 and
// its body writes that instance's `got`. The enable was dropped whole, the
// registry holding the task under its bare name alone, so `u1.got` stayed 0.
TEST(TaskSim, TaskEnabledByHierarchicalNameRunsInTheChildInstance) {
  auto val = RunAndGet(
      "module sub;\n"
      "  int got;\n"
      "  task tk(int d);\n"
      "    got = d;\n"
      "  endtask\n"
      "endmodule\n"
      "module t;\n"
      "  sub u1();\n"
      "  initial u1.tk(4);\n"
      "endmodule\n",
      "u1.got");
  EXPECT_EQ(val, 4u);
}

// §13.3.2 (printed page 339): a static task in each instance of a module has
// storage of its own, and §13.3 has the enable consume the body's delay before
// control returns. Enabled by hierarchical name from the top, the task's
// static `n` counts 1 at time 3 in u1, 1 at 8 in u2 and 2 at 10 in u1 again;
// one storage for both would read 2 at 8 and 3 at 10, and a body run without
// its delay would read every time as 0.
TEST(TaskSim, StaticLocalOfTaskEnabledByHierarchicalNameIsPerInstance) {
  auto val = RunAndGet(
      "module sub;\n"
      "  task tk(int d, output int r);\n"
      "    int n;\n"
      "    #d;\n"
      "    n++;\n"
      "    r = n * 100 + $time;\n"
      "  endtask\n"
      "endmodule\n"
      "module t;\n"
      "  int a, b, c;\n"
      "  logic [31:0] x;\n"
      "  sub u1();\n"
      "  sub u2();\n"
      "  initial begin\n"
      "    u1.tk(3, a);\n"
      "    u2.tk(5, b);\n"
      "    u1.tk(2, c);\n"
      "    x = a * 1000000 + b * 1000 + c;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 103108210u);
}

// §13.4 with §23.6: a function called by hierarchical name, `u1.twice(21)`,
// is the instance's, and its body reads the instance's own `k` -- 21, for
// 42 -- rather than the caller's `k` of 5, which would give 26; a call that
// found no function read 0.
TEST(TaskSim, FunctionCalledByHierarchicalNameReadsTheChildInstance) {
  auto val = RunAndGet(
      "module sub;\n"
      "  int k = 21;\n"
      "  function int twice(int v);\n"
      "    return v + k;\n"
      "  endfunction\n"
      "endmodule\n"
      "module t;\n"
      "  int k = 5;\n"
      "  logic [31:0] x;\n"
      "  sub u1();\n"
      "  initial x = u1.twice(21);\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

// §13.3 (printed page 335): a task may enable another task, which may enable
// still others, and control does not return to the enabling process until
// every task it enabled has completed; §8.13 (printed 190) lets a method
// name a method of its own class bare, on the object it runs on. `go(d)`
// enabled from inside `viabare`, itself enabled through the handle, was
// handed to the synchronous function interpreter, which ran the property
// write and dropped the `#d`, so the enable from the initial returned at 0
// with v already 1: the time reads 5 and the property 1, packed as 51 where
// the defect read 1.
TEST(TaskSim, ClassTaskEnabledByItsBareNameFromATaskConsumesItsDelay) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  class C;\n"
      "    int v;\n"
      "    task go(int d);\n"
      "      #d;\n"
      "      v = v + 1;\n"
      "    endtask\n"
      "    task viabare(int d);\n"
      "      go(d);\n"
      "    endtask\n"
      "  endclass\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    c.viabare(5);\n"
      "    x = $time * 10 + c.v;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 51u);
}

// §8.11 (printed page 187) has `this` denote the object the method was
// invoked on, so `this.go(d)` is the bare `go(d)` with its receiver written,
// and §13.3 has the enable return after the callee's delay. A second enable
// after the bare one reads 10 and a property of 2, packed as 102; the delay
// dropped in either enable reads a smaller time, and a write lost through
// the receiver reads 1.
TEST(TaskSim, ClassTaskEnabledThroughThisFromATaskConsumesItsDelay) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  class C;\n"
      "    int v;\n"
      "    task go(int d);\n"
      "      #d;\n"
      "      v = v + 1;\n"
      "    endtask\n"
      "    task viabare(int d);\n"
      "      go(d);\n"
      "    endtask\n"
      "    task viathis(int d);\n"
      "      this.go(d);\n"
      "    endtask\n"
      "  endclass\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    c.viabare(5);\n"
      "    c.viathis(5);\n"
      "    x = $time * 10 + c.v;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 102u);
}

// §8.15 (printed page 191): `super.go(d)` in a derived class's task names the
// base class's `go`, the one the derived `go` overrides, and §13.3 has the
// derived task go on only when that enable has completed. The base body
// waits `d` and adds 1; the override adds 10 with no wait. The direct enable
// through the derived handle reads the override, and `viasuper` after it
// reads the base's: time 5 and property 11, packed as 61. Dispatch through
// the object's class would add 10 more and wait nothing, 21; the base body
// run without its delay reads 11.
TEST(TaskSim, BaseClassTaskEnabledThroughSuperFromATaskConsumesItsDelay) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  class Base;\n"
      "    int v;\n"
      "    task go(int d);\n"
      "      #d;\n"
      "      v = v + 1;\n"
      "    endtask\n"
      "  endclass\n"
      "  class Der extends Base;\n"
      "    task go(int d);\n"
      "      v = v + 10;\n"
      "    endtask\n"
      "    task viasuper(int d);\n"
      "      super.go(d);\n"
      "    endtask\n"
      "  endclass\n"
      "  initial begin\n"
      "    Der d = new;\n"
      "    d.go(5);\n"
      "    d.viasuper(5);\n"
      "    x = $time * 10 + d.v;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 61u);
}

// §9.3.2 (printed page 226) with §8.15: a `fork ... join` in the base task
// reached through `super.run()` joins before the statement after it runs, and
// the derived task goes on only then. The branch's write at time 2 is read
// after the join, so the base packs 3 * 10 + 2 = 32 into the property and the
// derived task reads time 2: 2 * 100 + 32 = 232. A base body never run reads
// 0, and a join that does not wait reads 0 * 10 + 0 with the derived at 0.
TEST(TaskSim, BaseClassTaskWithAForkJoinEnabledThroughSuperJoinsFirst) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  class Base;\n"
      "    int v;\n"
      "    task run;\n"
      "      int r;\n"
      "      fork\n"
      "        #2 r = 3;\n"
      "        #1;\n"
      "      join\n"
      "      v = r * 10 + $time;\n"
      "    endtask\n"
      "  endclass\n"
      "  class Der extends Base;\n"
      "    task run;\n"
      "      super.run();\n"
      "      x = $time * 100 + v;\n"
      "    endtask\n"
      "  endclass\n"
      "  initial begin\n"
      "    Der d = new;\n"
      "    d.run();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 232u);
}

// §13.3 (printed pages 336-337): a tf_port_item takes a data_type_or_implicit,
// the implicit form being signing and packed dimensions alone, and a formal
// whose data type is not explicitly declared is `logic`, so `input [7:0] a`
// is an 8-bit logic vector and §13.5.1's copy-in takes the 9-bit actual's
// low byte: 9'h1AB into it reads 171. The parser left the formal at the
// implicit kind with its dimensions attached, and the bind sizes a formal of
// a declared type alone, so the formal kept all nine bits and read 427.
TEST(TaskSim, FormalWithAPackedDimensionAndNoTypeKeywordIsLogicOfThatWidth) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  task tk(input [7:0] a); r = a; endtask\n"
      "  initial tk(9'h1AB);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 171u);
}

// §13.3 (printed page 337): a formal with neither a type nor a direction
// inherits the previous formal's data type, and the clause's mytask4 has a
// `b` after `input [3:0][7:0] a` declared as an 8-bit-by-4 vector, so `b`
// after `input [7:0] a` is `logic [7:0]` and 9'h1CD into it reads 205. The
// inherited type was the unsized implicit one, so `b` kept 461.
TEST(TaskSim, UntypedFormalInheritsThePrecedingFormalsPackedDimension) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  task tk(input [7:0] a, b); r = a * 1000 + b; endtask\n"
      "  initial tk(9'h1AB, 9'h1CD);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 171205u);
}

// §13.3 (printed page 337): the first formal with no type and no dimension
// is a `logic` scalar, and an explicitly directed formal after a sized one
// starts over at that scalar rather than inheriting the size, so `output yy`
// after `output logic [15:0] uu, vv` holds one bit of the 3 written to it,
// while `vv` takes the 16 bits of `uu`: 65535 * 10 + 1 with 2 in the middle
// digit.
TEST(TaskSim, FormalWithNeitherTypeNorDimensionIsAScalarLogic) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [15:0] u, v; logic y; int r;\n"
      "  task tk(input [7:0] a, b, output logic [15:0] uu, vv, output yy);\n"
      "    uu = 16'hFFFF; vv = 2; yy = 3;\n"
      "  endtask\n"
      "  initial begin\n"
      "    tk(8'hAB, 9'h1CD, u, v, y);\n"
      "    r = u * 100 + v * 10 + y;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 6553521u);
}

// §13.3 (printed page 337): mytask4's `output [3:0][7:0] y[1:0]` is a formal
// with an unpacked dimension on the identifier and a packed two-dimensional
// element type, and the direction copies the value out at the end; §13.5
// (printed 348) has the return pass the output formals' values to the
// variables of the call. Each element of the caller's `y` takes the element
// the body wrote: 32'h01020304 into y[0] and a + b[2], 513 + 7, into y[1].
// The formal was bound as the per-element variables yo[0] and yo[1] and the
// copy-out looked for a variable named yo alone, so both elements of y kept
// their x and read 0; an element copied under the other's index would read
// the other's value.
TEST(TaskSim, OutputFormalWithAnUnpackedDimensionCopiesEachElementOut) {
  const char* src =
      "module t;\n"
      "  logic [3:0][7:0] y[1:0];\n"
      "  task mytask4(input [3:0][7:0] a, b[3:0], output [3:0][7:0] yo[1:0]);\n"
      "    yo[0] = 32'h01020304; yo[1] = a + b[2];\n"
      "  endtask\n"
      "  initial begin\n"
      "    logic [3:0][7:0] bb[3:0];\n"
      "    bb[2] = 7;\n"
      "    mytask4(513, bb, y);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "y[0]"), 0x01020304u);
  EXPECT_EQ(RunAndGet(src, "y[1]"), 520u);
}

// §7.4.1 (printed page 153): a packed array subdivides a vector into subfields
// addressed as elements, so `yo[1][3]` on the `[3:0][7:0]` element is the
// eight bits of subfield 3, bits 31 to 24, and writing 8'hAB there after
// `yo[1] = 1` leaves 32'hAB000001 for the copy-out. The formal's element
// variable carried no record of its packed dimensions, so the index addressed
// bit 3 of the element and the copy would have carried 32'h00000009.
TEST(TaskSim, OutputArrayFormalElementTakesAPackedSubfieldWriteInTheBody) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [3:0][7:0] y[1:0];\n"
      "  task tk(output [3:0][7:0] yo[1:0]);\n"
      "    yo[0] = 258; yo[1] = 1; yo[1][3] = 8'hAB;\n"
      "  endtask\n"
      "  initial tk(y);\n"
      "endmodule\n",
      "y[1]");
  EXPECT_EQ(val, 0xAB000001u);
}

// §13.3 (printed page 337): an output formal copies its value out at the end
// and nothing in at the beginning, so an element the body leaves alone carries
// back what the formal held from the start -- the 0 BindValueArg starts every
// output formal at -- and not the 32'hFFFFFFFF the caller's element held
// before the call, which a copy-in would have carried through the body.
TEST(TaskSim, OutputArrayFormalElementLeftUnwrittenCopiesItsDefaultOut) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [3:0][7:0] y[1:0];\n"
      "  task tk(output [3:0][7:0] yo[1:0]); yo[0] = 258; endtask\n"
      "  initial begin\n"
      "    y[1] = 32'hFFFFFFFF;\n"
      "    tk(y);\n"
      "  end\n"
      "endmodule\n",
      "y[1]");
  EXPECT_EQ(val, 0u);
}

// §13.3 (printed page 337): an inout formal copies in at the beginning and out
// at the end, so each element of `io` starts at the caller's element and the
// caller's element ends at what the body left: y[0] from 16 to 17 and y[1]
// from 5 to 5 + 2 with subfield 3 set to 8'hC0, 32'hC0000007. A lost copy-in
// reads 1 and 32'hC0000002; a lost copy-out reads 16 and 5.
TEST(TaskSim, InoutArrayFormalCopiesEachElementInAndOut) {
  const char* src =
      "module t;\n"
      "  logic [3:0][7:0] y[1:0];\n"
      "  task bump(inout [3:0][7:0] io[1:0]);\n"
      "    io[0] = io[0] + 1; io[1] = io[1] + 2; io[1][3] = 8'hC0;\n"
      "  endtask\n"
      "  initial begin\n"
      "    y[0] = 16; y[1] = 5;\n"
      "    bump(y);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "y[0]"), 17u);
  EXPECT_EQ(RunAndGet(src, "y[1]"), 0xC0000007u);
}

// §11.5.1 with §13.3: `zo[0][3]` on an `output [7:0] zo[1:0]` formal, one
// packed dimension, is bit 3 of element 0, so the bit set in the body reaches
// the caller's z[0] as 8 beside the 8'h5A copied into z[1]. A lost copy-out
// reads 0 for both; the bit landing on the wrong element reads 0x5A | 8.
TEST(TaskSim, OutputArrayFormalElementTakesABitSelectWriteInTheBody) {
  const char* src =
      "module t;\n"
      "  logic [7:0] z[1:0];\n"
      "  task tk(output [7:0] zo[1:0]);\n"
      "    zo[0] = 8'h00; zo[1] = 8'h5A; zo[0][3] = 1'b1;\n"
      "  endtask\n"
      "  initial tk(z);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "z[0]"), 8u);
  EXPECT_EQ(RunAndGet(src, "z[1]"), 0x5Au);
}

}  // namespace
