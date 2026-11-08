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
      "    static drv d = new;\n"
      "    x = 0;\n"
      "    d.run();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 50u);
}

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
      "    static drv d = new;\n"
      "    d.run();\n"
      "    y = $time;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 70u);
}

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
      "    static drv d = new;\n"
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
      "    static drv d = new;\n"
      "    x = 0;\n"
      "    d.run(41);\n"
      "    x = d.count;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

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
      "    static drv a = new;\n"
      "    static drv b = new;\n"
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
      "    static C c = new;\n"
      "    c.viabare(5);\n"
      "    x = $time * 10 + c.v;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 51u);
}

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
      "    static C c = new;\n"
      "    c.viabare(5);\n"
      "    c.viathis(5);\n"
      "    x = $time * 10 + c.v;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 102u);
}

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
      "    static Der d = new;\n"
      "    d.go(5);\n"
      "    d.viasuper(5);\n"
      "    x = $time * 10 + d.v;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 61u);
}

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
      "    static Der d = new;\n"
      "    d.run();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 232u);
}

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

TEST(TaskSim, ModuleFunctionFormalReadsATypedefDefinedBelowTheFunction) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct pair_t;\n"
                      "  function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "    return a.A.a * 10 + a.A.b;\n"
                      "  endfunction\n"
                      "  typedef struct { int a, b; } pair_t;\n"
                      "  int y;\n"
                      "  initial y = f(tagged A '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            34u);
}

TEST(TaskSim, ModuleTaskOutputFormalReadsATypedefDefinedBelowTheTask) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct pair_t;\n"
                      "  task tk(output union tagged { void N; pair_t A; }"
                      " o);\n"
                      "    o = tagged A '{3, 4};\n"
                      "  endtask\n"
                      "  typedef struct { int a, b; } pair_t;\n"
                      "  union tagged { void N; pair_t A; } p;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    tk(p);\n"
                      "    y = p.A.a * 10 + p.A.b;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            34u);
}

TEST(TaskSim, GenerateBlockFunctionFormalReadsATypedefDefinedBelowTheBlock) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct pair_t;\n"
                      "  if (1) begin : g\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 10 + a.A.b;\n"
                      "    endfunction\n"
                      "  end\n"
                      "  typedef struct { int a, b; } pair_t;\n"
                      "  int y;\n"
                      "  initial y = g.f(tagged A '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            34u);
}

TEST(TaskSim, GenerateForBlockFunctionFormalReadsATypedefDefinedBelowTheLoop) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct pair_t;\n"
                      "  for (genvar i = 0; i < 2; i++) begin : blk\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return i * 100 + a.A.a * 10 + a.A.b;\n"
                      "    endfunction\n"
                      "  end\n"
                      "  typedef struct { int a, b; } pair_t;\n"
                      "  int y;\n"
                      "  initial y = blk[0].f(tagged A '{3, 4})"
                      " + blk[1].f(tagged A '{5, 6});\n"
                      "endmodule\n",
                      "y"),
            190u);
}

TEST(TaskSim, GenerateCaseAndElseArmFunctionFormalsReadATypedefDefinedBelow) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct pair_t;\n"
                      "  case (2)\n"
                      "    1: begin : c function int f(int a); return 1;"
                      " endfunction end\n"
                      "    2: begin : c\n"
                      "      function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "        return a.A.a * 10 + a.A.b;\n"
                      "      endfunction\n"
                      "    end\n"
                      "  endcase\n"
                      "  if (0) begin : e end\n"
                      "  else begin : e\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.b * 10 + a.A.a;\n"
                      "    endfunction\n"
                      "  end\n"
                      "  typedef struct { int a, b; } pair_t;\n"
                      "  int y;\n"
                      "  initial y = c.f(tagged A '{7, 8}) + e.f(tagged A"
                      " '{1, 2});\n"
                      "endmodule\n",
                      "y"),
            99u);
}

TEST(TaskSim, GenerateBlockFunctionFormalReadsTheBlocksOwnTypedefDefinedBelow) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  if (1) begin : g\n"
                      "    typedef struct pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 10 + a.A.b;\n"
                      "    endfunction\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.f(tagged A '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            34u);
}

TEST(TaskSim, NestedGenerateBlockFunctionFormalsReadTypedefsDefinedBelowThem) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  if (1) begin : g\n"
                      "    if (1) begin : h\n"
                      "      typedef struct pair_t;\n"
                      "      function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "        return a.A.a * 10 + a.A.b;\n"
                      "      endfunction\n"
                      "      typedef struct { int a, b; } pair_t;\n"
                      "    end\n"
                      "    typedef struct duo_t;\n"
                      "    if (1) begin : k\n"
                      "      function int f(union tagged { void N; duo_t D; }"
                      " a);\n"
                      "        return a.D.b * 10 + a.D.a;\n"
                      "      endfunction\n"
                      "    end\n"
                      "    typedef struct { int a, b; } duo_t;\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.h.f(tagged A '{3, 4})"
                      " + g.k.f(tagged D '{5, 6});\n"
                      "endmodule\n",
                      "y"),
            99u);
}

TEST(TaskSim, GenerateForBlockFunctionFormalReadsTheBlocksOwnTypedefBelowIt) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  for (genvar i = 0; i < 2; i++) begin : blk\n"
                      "    typedef struct pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return i * 100 + a.A.b * 10 + a.A.a;\n"
                      "    endfunction\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = blk[0].f(tagged A '{1, 2})"
                      " + blk[1].f(tagged A '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            164u);
}

}  // namespace
