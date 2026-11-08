#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"

using namespace delta;

TEST(NonblockingAssignSchedulingSim, SchedulesUpdateInNbaRegion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst, snap;\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    snap = 8'd0;\n"
      "    dst <= 8'd7;\n"
      "    snap = dst;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("snap")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 7u);
}

TEST(NonblockingAssignSchedulingSim, ZeroDelaySchedulesInCurrentTimestep) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    dst <= 8'd5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 5u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

TEST(NonblockingAssignSchedulingSim, NonzeroDelaySchedulesAsFutureEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst, mid;\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    mid = 8'd0;\n"
      "    dst <= #10 8'd99;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 mid = dst;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("mid")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 99u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 10u);
}

TEST(NonblockingAssignSchedulingSim, RhsUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, dst;\n"
      "  initial begin\n"
      "    src = 8'd5;\n"
      "    dst = 8'd0;\n"
      "    dst <= src;\n"
      "    src = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("src")->value.ToUint64(), 99u);
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 5u);
}

TEST(NonblockingAssignSchedulingSim, LhsTargetUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:1];\n"
      "  int idx;\n"
      "  initial begin\n"
      "    mem[0] = 8'd0;\n"
      "    mem[1] = 8'd0;\n"
      "    idx = 0;\n"
      "    mem[idx] <= 8'hCC;\n"
      "    idx = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("mem[0]")->value.ToUint64(), 0xCCu);
  EXPECT_EQ(f.ctx.FindVariable("mem[1]")->value.ToUint64(), 0u);
}

TEST(NonblockingAssignSchedulingSim,
     LhsBitSelectTargetUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  int idx;\n"
      "  initial begin\n"
      "    dst = 8'h00;\n"
      "    idx = 0;\n"
      "    dst[idx] <= 1'b1;\n"
      "    idx = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 0x01u);
}

TEST(NonblockingAssignSchedulingSim, ConcurrentNbaWritesUsePreUpdateValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = 8'd2;\n"
      "    a <= b;\n"
      "    b <= a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 1u);
}

TEST(NonblockingAssignSchedulingSim,
     ClockedNonblockingUpdateDeferredToNbaRegion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] d, q, snap;\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    d = 8'hAB;\n"
      "    q = 8'h00;\n"
      "    snap = 8'h00;\n"
      "    #5 clk = 1'b1;\n"
      "  end\n"
      "  always @(posedge clk) begin\n"
      "    q <= d;\n"
      "    snap = q;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("snap")->value.ToUint64(), 0x00u);
  EXPECT_EQ(f.ctx.FindVariable("q")->value.ToUint64(), 0xABu);
}

static void ExpectSelectNbaWritesNothingAndKeepsItsEvent(const std::string& src,
                                                         SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  auto& pool = f.scheduler.GetEventPool();
  constexpr size_t kPrimedEvents = 32;
  std::vector<Event*> primed;
  primed.reserve(kPrimedEvents);
  for (size_t n = 0; n < kPrimedEvents; ++n) primed.push_back(pool.Acquire());
  for (auto* e : primed) pool.Release(e);
  ASSERT_EQ(pool.FreeCount(), kPrimedEvents);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 0x00u);
  EXPECT_EQ(pool.FreeCount(), kPrimedEvents);
}

TEST(NonblockingAssignSchedulingSim,
     DroppedUnknownIndexSelectNbaReturnsItsEvent) {
  SimFixture f;
  ExpectSelectNbaWritesNothingAndKeepsItsEvent(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [2:0] i;\n"
      "  initial begin\n"
      "    x = 8'h00;\n"
      "    x[i] <= 1'b1;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
}

TEST(NonblockingAssignSchedulingSim,
     DroppedOutOfRangePartSelectNbaReturnsItsEvent) {
  SimFixture f;
  ExpectSelectNbaWritesNothingAndKeepsItsEvent(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'h00;\n"
      "    x[9:8] <= 2'b11;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
}

TEST(NonblockingAssignSchedulingSim,
     LhsConcatBitSelectTargetUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int idx;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    b = 8'h00;\n"
      "    idx = 0;\n"
      "    {a[idx], b} <= 9'b1_0101_0101;\n"
      "    idx = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0x01u);
  EXPECT_EQ(vb->value.ToUint64(), 0x55u);
}

TEST(NonblockingAssignSchedulingSim,
     LhsConcatPartSelectOffsetUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int idx;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    b = 8'h00;\n"
      "    idx = 0;\n"
      "    {a[idx +: 4], b} <= 12'hC5A;\n"
      "    idx = 4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* target = f.ctx.FindVariable("a");
  ASSERT_NE(target, nullptr);
  EXPECT_EQ(target->value.ToUint64(), 0x0Cu);
  auto* rest = f.ctx.FindVariable("b");
  ASSERT_NE(rest, nullptr);
  EXPECT_EQ(rest->value.ToUint64(), 0x5Au);
  auto* offset = f.ctx.FindVariable("idx");
  ASSERT_NE(offset, nullptr);
  EXPECT_EQ(offset->value.ToUint64(), 4u);
}

TEST(NonblockingAssignSchedulingSim,
     LhsStreamingConcatWithRangeUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [0:3];\n"
      "  int idx;\n"
      "  initial begin\n"
      "    idx = 0;\n"
      "    {>> {arr with [idx +: 2]}} <= 16'hABCD;\n"
      "    idx = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  const std::pair<const char*, uint64_t> kWanted[] = {
      {"arr[0]", 0xABu}, {"arr[1]", 0xCDu}, {"arr[2]", 0u}, {"arr[3]", 0u}};
  for (const auto& [name, wanted] : kWanted) {
    auto* element = f.ctx.FindVariable(name);
    ASSERT_NE(element, nullptr) << "Variable not found: " << name;
    EXPECT_EQ(element->value.ToUint64(), wanted) << "Variable: " << name;
  }
}

static void ExpectSampledStructSurvivesMemberDeposit(const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors) << "source reported an elaboration error";
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* target = f.ctx.FindVariable("d");
  ASSERT_NE(target, nullptr);
  EXPECT_EQ(target->value.ToUint64(), 0xAABBu);
  auto* sampled = f.ctx.FindVariable("s");
  ASSERT_NE(sampled, nullptr);
  EXPECT_EQ(sampled->value.ToUint64(), 0x00BBu);
}

TEST(NonblockingAssignSchedulingSim, SampledRhsSurvivesMemberDeposit) {
  ExpectSampledStructSurvivesMemberDeposit(
      "module t;\n"
      "  typedef struct packed { logic [7:0] b; logic [7:0] l; } pair_t;\n"
      "  pair_t s;\n"
      "  logic [15:0] d;\n"
      "  initial begin\n"
      "    d = 16'h1234;\n"
      "    s = 16'hAABB;\n"
      "    d <= s;\n"
      "    s.b = 8'h00;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n");
}

TEST(NonblockingAssignSchedulingSim, EventControlRhsSurvivesMemberDeposit) {
  ExpectSampledStructSurvivesMemberDeposit(
      "module t;\n"
      "  typedef struct packed { logic [7:0] b; logic [7:0] l; } pair_t;\n"
      "  pair_t s;\n"
      "  logic [15:0] d;\n"
      "  logic clk;\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    d = 16'h1234;\n"
      "    s = 16'hAABB;\n"
      "    d <= @(posedge clk) s;\n"
      "  end\n"
      "  initial begin\n"
      "    #2;\n"
      "    s.b = 8'h00;\n"
      "    #3;\n"
      "    clk = 1'b1;\n"
      "  end\n"
      "endmodule\n");
}
