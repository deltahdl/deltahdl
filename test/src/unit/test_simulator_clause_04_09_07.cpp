#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

using namespace delta;

// §4.9.7 atom: copy-in is timed to invocation. The argument value is
// captured into the formal at the moment the call is made, before the body
// runs — so a caller-side source mutation that happens later inside the
// task body must not propagate to the formal. Production: `BindFunctionArgs`
// (src/simulator/eval_function.cpp:418) calls `ResolveArgValue` and writes
// the result into a freshly created local variable; that local is never
// re-read from the caller's storage. Observed by `cap = read_then_clobber(src)`
// where the body writes `src = 99` after capturing `v` into `seen`. If
// copy-in were a reference (or deferred until a later body read), `seen`
// would observe 99; the test asserts 5, so the snapshot was taken at
// invocation.
TEST(SubroutineArgSchedulingSim, CopyInCapturesValueAtInvocation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int src, seen;\n"
      "  function int read_then_clobber(input int v);\n"
      "    src = 99;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 5;\n"
      "    seen = read_then_clobber(src);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("seen")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("src")->value.ToUint64(), 99u);
}

// §4.9.7 atom: copy-out is timed to return. The caller's storage is not
// touched until the subroutine returns — a parallel observer reading the
// caller variable while the task is suspended mid-body must see the
// pre-call value, and only after the return statement does the writeback
// land. Production: `WritebackOutputArgs` (src/simulator/eval_function.cpp:445)
// runs from `TeardownTaskCall` (line 1474) at the end of the task body, not
// at the assignment statement that wrote the formal. Observed with a #5
// delay between `o = 8'd42;` and the implicit return: a parallel `initial`
// reads `dst` at #2 (mid-call) and again at #10 (post-return).
TEST(SubroutineArgSchedulingSim, CopyOutOccursOnReturn) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst, mid_call, after_return;\n"
      "  task set_then_delay(output logic [7:0] o);\n"
      "    o = 8'd42;\n"
      "    #5;\n"
      "  endtask\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    mid_call = 8'd0;\n"
      "    after_return = 8'd0;\n"
      "    set_then_delay(dst);\n"
      "    after_return = dst;\n"
      "  end\n"
      "  initial begin\n"
      "    #2 mid_call = dst;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("mid_call")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 42u);
  EXPECT_EQ(f.ctx.FindVariable("after_return")->value.ToUint64(), 42u);
}

// §4.9.7 atom: the copy-out behaves the same as a blocking assignment.
// Production: `WritebackOutputArgs` calls `PerformBlockingAssign` at
// src/simulator/eval_function.cpp:457 — literally the same code path used
// for `=` statements. The observable consequence is immediate visibility
// to the next statement in the same process: the post-call read sees the
// written-back value without waiting for any later region. If copy-out
// were routed through NBA scheduling, `snap` would still be 0 because the
// blocking read of `dst` would race ahead of the deferred update.
TEST(SubroutineArgSchedulingSim, CopyOutImmediatelyVisibleToNextStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst, snap;\n"
      "  task write_dst(output logic [7:0] o);\n"
      "    o = 8'd5;\n"
      "  endtask\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    snap = 8'd0;\n"
      "    write_dst(dst);\n"
      "    snap = dst;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("snap")->value.ToUint64(), 5u);
}

// §4.9.7 atom 4 corollary: a blocking-style commit fires variable watchers
// the same way a `=` statement does. Production: `PerformBlockingAssign`
// updates the variable in place, which triggers `NotifyWatchers` on the
// caller-side `Variable`. An `always @(dst)` block treats the copy-out as
// an event source. Observed by `observed` flipping to 1 after the call
// returns — if copy-out bypassed the watcher path (e.g., wrote storage
// directly without notifying), `observed` would stay 0.
TEST(SubroutineArgSchedulingSim, CopyOutTriggersWatchers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst, observed;\n"
      "  task bump(output logic [7:0] o);\n"
      "    o = 8'd9;\n"
      "  endtask\n"
      "  always @(dst) observed = 8'd1;\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    observed = 8'd0;\n"
      "    bump(dst);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 9u);
  EXPECT_EQ(f.ctx.FindVariable("observed")->value.ToUint64(), 1u);
}

// §4.9.7 inout atom: an inout argument exercises both copy-in (atom 2)
// and copy-out (atom 3) on the same formal. Production: `BindFunctionArgs`
// runs the same ResolveArgValue/CreateLocalVariable copy-in that input
// args get; `WritebackOutputArgs` (line 449) also writes back when
// `dir == Direction::kInout`. Observed by `inc(x)` where the body reads
// the caller's value (10), increments locally to 11, and writes back —
// this only succeeds end-to-end if copy-in and copy-out both fire.
TEST(SubroutineArgSchedulingSim, InoutArgCopiesInThenOut) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task inc(inout logic [7:0] v);\n"
      "    v = v + 8'd1;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    inc(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 11u);
}

// §4.9.7 edge: "on return" includes early-return paths. The body assigns
// `o = 8'd5` and then takes the `return;` branch before reaching the
// later `o = 8'd99` assignment — copy-out must still fire, and the
// caller variable must hold the value the formal had at the return
// moment (5, not 99). Production: `TeardownTaskCall`
// (src/simulator/eval_function.cpp:1474) calls `WritebackOutputArgs`
// unconditionally after `ExecFunctionBody`; the body's `kReturn`
// `StmtResult` short-circuits the inner statement loop without
// suppressing the outer writeback. A bug that gated writeback on
// "natural fall-through" (kNormal) would leave `dst == 0`; a bug that
// kept executing past the return would leave `dst == 99`.
TEST(SubroutineArgSchedulingSim, CopyOutFiresOnEarlyReturn) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  task set_and_skip(output logic [7:0] o, input bit do_skip);\n"
      "    o = 8'd5;\n"
      "    if (do_skip) return;\n"
      "    o = 8'd99;\n"
      "  endtask\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    set_and_skip(dst, 1'b1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 5u);
}

// §4.9.7 atom 4 edge: "behaves the same as does any blocking assignment"
// implies the writeback supports the same LHS forms a `=` statement
// supports — bit-select, element-select, slice, concat. The output
// actual here is `arr[2]`, an element-select on an unpacked array.
// Production: `WritebackOutputArgs` calls `PerformBlockingAssign(arr[2],
// formal_value, ...)`, which dispatches into the same select-LHS path
// (src/simulator/statement_assign_core.cpp PerformBlockingAssign) used
// by direct `arr[2] = ...;` statements. If copy-out had its own
// simplified writeback that only handled bare-identifier LHS, `arr[2]`
// would stay 0 and the test would fail; a sibling read of `arr[1]`
// proves the writeback is targeted, not a wholesale array clobber.
TEST(SubroutineArgSchedulingSim, CopyOutSupportsBlockingAssignLhsForms) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [0:3];\n"
      "  logic [7:0] sibling;\n"
      "  task write_one(output logic [7:0] o);\n"
      "    o = 8'd42;\n"
      "  endtask\n"
      "  initial begin\n"
      "    arr[0] = 8'd0;\n"
      "    arr[1] = 8'd7;\n"
      "    arr[2] = 8'd0;\n"
      "    arr[3] = 8'd0;\n"
      "    write_one(arr[2]);\n"
      "    sibling = arr[1];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 42u);
  EXPECT_EQ(f.ctx.FindVariable("sibling")->value.ToUint64(), 7u);
}

// §4.9.7 atom 3 plural form: every output formal is written back on
// return — `WritebackOutputArgs` iterates `func->func_args` and writes
// each kOutput/kInout in order. The single-arg form would pass even if
// the writeback loop terminated after the first arg; this case proves
// that all three caller-side variables are committed.
TEST(SubroutineArgSchedulingSim, MultipleOutputArgsAllWrittenOnReturn) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  task triple(output logic [7:0] x, y, z);\n"
      "    x = 8'd1;\n"
      "    y = 8'd2;\n"
      "    z = 8'd3;\n"
      "  endtask\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    b = 8'd0;\n"
      "    c = 8'd0;\n"
      "    triple(a, b, c);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 3u);
}
