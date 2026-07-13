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

// Copy-out to a part-select actual. Because the copy-out is a blocking
// assignment, binding the output formal to a part-select of a wider vector must
// update only the selected bits and leave the rest of the vector as it was --
// exactly what a direct blocking assignment to that part-select would do.
TEST(SubroutineArgSchedulingSim, CopyOutToPartSelectActualLikeBlockingAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] vec;\n"
      "  task write_nibble(output logic [3:0] o);\n"
      "    o = 4'hA;\n"
      "  endtask\n"
      "  initial begin\n"
      "    vec = 8'hF0;\n"
      "    write_nibble(vec[3:0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("vec")->value.ToUint64(), 0xFAu);
}

// Copy-out to a concatenation lvalue actual. A blocking assignment accepts a
// concatenation on its left, distributing the source across the concatenated
// targets; the copy-out, behaving the same way, must split the returned value
// across the two variables bound by the concatenation.
TEST(SubroutineArgSchedulingSim,
     CopyOutToConcatenationActualLikeBlockingAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] hi, lo;\n"
      "  task write_byte(output logic [7:0] o);\n"
      "    o = 8'hC3;\n"
      "  endtask\n"
      "  initial begin\n"
      "    hi = 4'h0;\n"
      "    lo = 4'h0;\n"
      "    write_byte({hi, lo});\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("hi")->value.ToUint64(), 0xCu);
  EXPECT_EQ(f.ctx.FindVariable("lo")->value.ToUint64(), 0x3u);
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

// Negative form of the copy-out rule. By-value passing makes an input formal a
// wholly independent local copy: the copy happens in on invocation, but nothing
// copies out on return for an input direction. So mutating the formal inside
// the subroutine must leave the caller's actual untouched even after the call
// returns -- the opposite of the output-argument writeback exercised above, and
// the boundary that distinguishes by-value input passing from
// pass-by-reference.
TEST(SubroutineArgSchedulingSim, InputFormalWriteDoesNotCopyOutToActual) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] actual;\n"
      "  task clobber_input(input logic [7:0] v);\n"
      "    v = 8'd200;\n"
      "  endtask\n"
      "  initial begin\n"
      "    actual = 8'd7;\n"
      "    clobber_input(actual);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("actual")->value.ToUint64(), 7u);
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
