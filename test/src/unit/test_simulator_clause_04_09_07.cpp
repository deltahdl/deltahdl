#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

using namespace delta;

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

// A non-void function delivers two distinct results on return: its return
// value, and the copy-out of any output argument. These travel through the
// function-call evaluation path (not the task-call statement path), so the
// copy-out is exercised here on that separate production path while confirming
// it does not disturb the returned value.
TEST(SubroutineArgSchedulingSim,
     OutputArgAndReturnValueBothDeliveredFromFunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] outv, ret;\n"
      "  function logic [7:0] compute(output logic [7:0] o);\n"
      "    o = 8'd7;\n"
      "    return 8'd200;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    outv = 8'd0;\n"
      "    ret = 8'd0;\n"
      "    ret = compute(outv);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("outv")->value.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("ret")->value.ToUint64(), 200u);
}

// Because the copy-out is a blocking assignment, it adapts the value to the
// width of the target the same way a direct blocking assignment would: an
// output formal wider than the actual it is bound to truncates on return.
TEST(SubroutineArgSchedulingSim,
     CopyOutTruncatesToTargetWidthLikeBlockingAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  task widen(output logic [7:0] o);\n"
      "    o = 8'd255;\n"
      "  endtask\n"
      "  initial begin\n"
      "    narrow = 4'd0;\n"
      "    widen(narrow);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("narrow")->value.ToUint64(), 0xFu);
}

TEST(SubroutineArgSchedulingSim, MultipleOutputArgsAllWrittenOnReturn) {
  SimFixture f;
  auto* design =
      ElaborateLowerRun(f,
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
                        "endmodule\n");
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 3u);
}
