#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(VirtualInterfaceClockingSim, LoweringSucceedsForVifWithClockingBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface SyncBus(input logic clk);\n"
      "  logic a, b, c;\n"
      "  clocking sb @(posedge clk);\n"
      "    input a; output b; inout c;\n"
      "  endclocking\n"
      "endinterface\n"
      "typedef virtual SyncBus VI;\n"
      "module top;\n"
      "  logic clk;\n"
      "  SyncBus u(clk);\n"
      "  VI v;\n"
      "  initial v = u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceClockingSim, ReadClockingInputViaVifReturnsSampledValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface SyncBus(input logic clk);\n"
      "  logic a;\n"
      "  clocking sb @(posedge clk); input a; endclocking\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk;\n"
      "  SyncBus u(clk);\n"
      "  virtual SyncBus v;\n"
      "  logic observed;\n"
      "  task do_read(virtual SyncBus h); observed = h.sb.a; endtask\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    u.a = 1;\n"
      "    v = u;\n"
      "    @(posedge clk);\n"
      "    do_read(v);\n"
      "  end\n"
      "  initial begin\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* observed = f.ctx.FindVariable("top.observed");
  ASSERT_NE(observed, nullptr);
  EXPECT_EQ(observed->value.ToUint64(), 1u);
}

TEST(VirtualInterfaceClockingSim,
     NonBlockingAssignToClockingOutputViaVifDrivesSignal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface SyncBus(input logic clk);\n"
      "  logic b;\n"
      "  clocking sb @(posedge clk); output b; endclocking\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk;\n"
      "  SyncBus u(clk);\n"
      "  virtual SyncBus v;\n"
      "  task do_drive(virtual SyncBus h); h.sb.b <= 1; endtask\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    u.b = 0;\n"
      "    v = u;\n"
      "    @(posedge clk);\n"
      "    do_drive(v);\n"
      "    @(posedge clk);\n"
      "  end\n"
      "  initial begin\n"
      "    #5 clk = 1;\n"
      "    #10 clk = 0;\n"
      "    #15 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* signal = f.ctx.FindVariable("top.u.b");
  ASSERT_NE(signal, nullptr);
  EXPECT_EQ(signal->value.ToUint64(), 1u);
}

TEST(VirtualInterfaceClockingSim,
     IntraAssignmentCycleDelayViaVifDefersDrive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface SyncBus(input logic clk);\n"
      "  logic c;\n"
      "  clocking sb @(posedge clk); inout c; endclocking\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk;\n"
      "  SyncBus u(clk);\n"
      "  virtual SyncBus v;\n"
      "  logic after_one, after_two;\n"
      "  task do_drive(virtual SyncBus h); h.sb.c <= ##1 1; endtask\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    u.c = 0;\n"
      "    v = u;\n"
      "    @(posedge clk);\n"
      "    do_drive(v);\n"
      "    @(posedge clk);\n"
      "    after_one = u.c;\n"
      "    @(posedge clk);\n"
      "    after_two = u.c;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 clk = 1;\n"
      "    #10 clk = 0;\n"
      "    #15 clk = 1;\n"
      "    #20 clk = 0;\n"
      "    #25 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* after_one = f.ctx.FindVariable("top.after_one");
  auto* after_two = f.ctx.FindVariable("top.after_two");
  ASSERT_NE(after_one, nullptr);
  ASSERT_NE(after_two, nullptr);
  EXPECT_EQ(after_one->value.ToUint64(), 0u);
  EXPECT_EQ(after_two->value.ToUint64(), 1u);
}

TEST(VirtualInterfaceClockingSim,
     ArrayOfVirtualInterfaceIndexedAccessRoutesToDistinctInstances) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface SyncBus(input logic clk);\n"
      "  logic b;\n"
      "  clocking sb @(posedge clk); output b; endclocking\n"
      "endinterface\n"
      "typedef virtual SyncBus VI;\n"
      "module top;\n"
      "  logic clk;\n"
      "  SyncBus u1(clk), u2(clk);\n"
      "  task do_drive(VI h); h.sb.b <= 1; endtask\n"
      "  initial begin\n"
      "    VI v[2] = '{ u1, u2 };\n"
      "    clk = 0;\n"
      "    u1.b = 0;\n"
      "    u2.b = 0;\n"
      "    @(posedge clk);\n"
      "    do_drive(v[1]);\n"
      "    @(posedge clk);\n"
      "  end\n"
      "  initial begin\n"
      "    #5 clk = 1;\n"
      "    #10 clk = 0;\n"
      "    #15 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* driven = f.ctx.FindVariable("top.u2.b");
  auto* untouched = f.ctx.FindVariable("top.u1.b");
  ASSERT_NE(driven, nullptr);
  ASSERT_NE(untouched, nullptr);
  EXPECT_EQ(driven->value.ToUint64(), 1u);
  EXPECT_EQ(untouched->value.ToUint64(), 0u);
}

}  // namespace
