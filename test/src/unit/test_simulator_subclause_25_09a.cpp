#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(VirtualInterfaceSim, UnassignedVariableReadsAsNull) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  bit is_null;\n"
      "  initial is_null = (vif == null);\n"
      "endmodule\n",
      f, "top.is_null");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(VirtualInterfaceSim, AssignNullThenComparePositive) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  bit is_null;\n"
      "  initial begin\n"
      "    vif = null;\n"
      "    is_null = (vif == null);\n"
      "  end\n"
      "endmodule\n",
      f, "top.is_null");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(VirtualInterfaceSim, AssignedInstanceNotEqualToNull) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  simple_bus u();\n"
      "  virtual simple_bus vif;\n"
      "  bit is_null;\n"
      "  initial begin\n"
      "    vif = u;\n"
      "    is_null = (vif == null);\n"
      "  end\n"
      "endmodule\n",
      f, "top.is_null");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(VirtualInterfaceSim, NullDereferenceIsFatalError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; logic a; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    vif = null;\n"
      "    x = vif.a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference through a null virtual interface", 7,
                            "25.9"));
}

TEST(VirtualInterfaceSim, UninitializedDereferenceIsFatalError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; logic a; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  initial x = vif.a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference through a null virtual interface", 5,
                            "25.9"));
}

TEST(VirtualInterfaceSim, InitializedComponentReadReflectsInstance) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "interface simple_bus; logic [7:0] a; endinterface\n"
      "module top;\n"
      "  simple_bus u();\n"
      "  virtual simple_bus vif;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    u.a = 8'h5A;\n"
      "    vif = u;\n"
      "    x = vif.a;\n"
      "  end\n"
      "endmodule\n",
      f, "top.x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5Au);
}

TEST(VirtualInterfaceSim, ReboundInstanceReflectsNewTarget) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; logic [7:0] a; endinterface\n"
      "module top;\n"
      "  simple_bus u1();\n"
      "  simple_bus u2();\n"
      "  virtual simple_bus vif;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    u1.a = 8'h11;\n"
      "    u2.a = 8'h22;\n"
      "    vif = u1;\n"
      "    x = vif.a;\n"
      "    vif = u2;\n"
      "    y = vif.a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("top.x");
  auto* y = f.ctx.FindVariable("top.y");
  ASSERT_NE(x, nullptr);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x11u);
  EXPECT_EQ(y->value.ToUint64(), 0x22u);
}

TEST(VirtualInterfaceSim, NullReferenceIsReportedAtTheReference) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; logic a; endinterface\n"
      "module top;\n"
      "  simple_bus u();\n"
      "  virtual simple_bus bound_vif;\n"
      "  virtual simple_bus null_vif;\n"
      "  logic x, y;\n"
      "  initial begin\n"
      "    bound_vif = u;\n"
      "    null_vif = null;\n"
      "    x = bound_vif.a;\n"
      "    y = null_vif.a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference through a null virtual interface", 11,
                            "25.9"));
}

TEST(VirtualInterfaceSim, NullReferenceNames25_9) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface plain_bus; logic q; endinterface\n"
      "module top;\n"
      "  virtual plain_bus vb;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    vb = null;\n"
      "    y = vb.q;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference through a null virtual interface", 7,
                            "25.9"));
}

TEST(VirtualInterfaceSim, NonblockingComponentWriteReachesInstance) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "interface simple_bus;\n"
      "  logic req;\n"
      "endinterface\n"
      "module top;\n"
      "  simple_bus u();\n"
      "  virtual simple_bus vif;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    u.req = 1'b0;\n"
      "    vif = u;\n"
      "    vif.req <= 1'b1;\n"
      "    #1 r = u.req;\n"
      "  end\n"
      "endmodule\n",
      f, "top.r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(VirtualInterfaceSim, BlockingComponentWriteReachesInstance) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface wide_bus;\n"
      "  logic [7:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  wide_bus dut();\n"
      "  virtual wide_bus vh;\n"
      "  logic [7:0] echo;\n"
      "  initial begin\n"
      "    dut.data = 8'h00;\n"
      "    vh = dut;\n"
      "    vh.data = 8'hC3;\n"
      "    echo = vh.data;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* on_instance = f.ctx.FindVariable("top.dut.data");
  ASSERT_NE(on_instance, nullptr);
  EXPECT_EQ(on_instance->value.ToUint64(), 0xC3u);
  auto* through_handle = f.ctx.FindVariable("top.echo");
  ASSERT_NE(through_handle, nullptr);
  EXPECT_EQ(through_handle->value.ToUint64(), 0xC3u);
}

TEST(VirtualInterfaceSim, WriteThroughNullVirtualInterfaceIsReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface tiny_bus;\n"
      "  logic q;\n"
      "endinterface\n"
      "module top;\n"
      "  tiny_bus w();\n"
      "  virtual tiny_bus held;\n"
      "  virtual tiny_bus dropped;\n"
      "  initial begin\n"
      "    held = w;\n"
      "    dropped = null;\n"
      "    held.q = 1'b0;\n"
      "    dropped.q = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference through a null virtual interface", 12,
                            "25.9"));
}

TEST(VirtualInterfaceSim, EventControlPosedgeThroughVirtualInterface) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic clk; endinterface\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  virtual bus_if v;\n"
                      "  integer x;\n"
                      "  initial begin\n"
                      "    x = 0;\n"
                      "    dif.clk = 1;\n"
                      "    v = dif;\n"
                      "    @(posedge v.clk);\n"
                      "    x = $time;\n"
                      "  end\n"
                      "  initial begin\n"
                      "    #10 dif.clk = 0;\n"
                      "    #20 dif.clk = 1;\n"
                      "  end\n"
                      "  initial #200 $finish;\n"
                      "endmodule\n",
                      "top.x"),
            30u);
}

TEST(VirtualInterfaceSim, EventControlLevelThroughVirtualInterface) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic clk; endinterface\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  virtual bus_if v;\n"
                      "  integer x;\n"
                      "  initial begin\n"
                      "    x = 0;\n"
                      "    dif.clk = 1;\n"
                      "    v = dif;\n"
                      "    @(v.clk);\n"
                      "    x = $time;\n"
                      "  end\n"
                      "  initial begin\n"
                      "    #20 dif.clk = 0;\n"
                      "    #40 dif.clk = 1;\n"
                      "  end\n"
                      "  initial #200 $finish;\n"
                      "endmodule\n",
                      "top.x"),
            20u);
}

TEST(VirtualInterfaceSim, OrListEventControlThroughVirtualInterface) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic a, b; endinterface\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  virtual bus_if v;\n"
                      "  integer x;\n"
                      "  initial begin\n"
                      "    x = 0;\n"
                      "    dif.a = 0;\n"
                      "    dif.b = 0;\n"
                      "    v = dif;\n"
                      "    @(v.a or v.b);\n"
                      "    x = $time;\n"
                      "  end\n"
                      "  initial begin\n"
                      "    #35 dif.b = 1;\n"
                      "    #35 dif.a = 1;\n"
                      "  end\n"
                      "  initial #200 $finish;\n"
                      "endmodule\n",
                      "top.x"),
            35u);
}

TEST(VirtualInterfaceSim, CompoundEventControlThroughVirtualInterface) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic a, b; endinterface\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  virtual bus_if v;\n"
                      "  integer x;\n"
                      "  initial begin\n"
                      "    x = 0;\n"
                      "    dif.a = 0;\n"
                      "    dif.b = 0;\n"
                      "    v = dif;\n"
                      "    @(v.a & v.b);\n"
                      "    x = $time;\n"
                      "  end\n"
                      "  initial begin\n"
                      "    #15 dif.a = 1;\n"
                      "    #25 dif.b = 1;\n"
                      "  end\n"
                      "  initial #200 $finish;\n"
                      "endmodule\n",
                      "top.x"),
            40u);
}

TEST(VirtualInterfaceSim, EventControlThroughNullVirtualInterfaceIsReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface bus_if; logic clk; endinterface\n"
      "module top;\n"
      "  bus_if dif();\n"
      "  virtual bus_if v;\n"
      "  initial begin\n"
      "    v = null;\n"
      "    @(posedge v.clk);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference through a null virtual interface", 7,
                            "25.9"));
}

TEST(VirtualInterfaceSim,
     CompoundEventControlThroughNullVirtualInterfaceIsReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface bus_if; logic a, b; endinterface\n"
      "module top;\n"
      "  bus_if dif();\n"
      "  virtual bus_if v;\n"
      "  initial begin\n"
      "    @(v.a & v.b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference through a null virtual interface", 6,
                            "25.9"));
}

TEST(VirtualInterfaceSim, ClassPropertyBoundFromModuleReadsInstanceComponent) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "class drv;\n"
                      "  virtual bus_if vif;\n"
                      "  function bit [7:0] rd();\n"
                      "    return vif.a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  drv d;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    dif.a = 8'h35;\n"
                      "    d = new;\n"
                      "    d.vif = dif;\n"
                      "    x = d.rd();\n"
                      "  end\n"
                      "endmodule\n",
                      "top.x"),
            0x35u);
}

TEST(VirtualInterfaceSim, ClassTaskWritesInstanceComponentThroughProperty) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "class drv;\n"
                      "  virtual bus_if vif;\n"
                      "  task run();\n"
                      "    vif.a <= 8'h35;\n"
                      "  endtask\n"
                      "endclass\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  drv d;\n"
                      "  initial begin\n"
                      "    d = new;\n"
                      "    d.vif = dif;\n"
                      "    d.run();\n"
                      "  end\n"
                      "endmodule\n",
                      "top.dif.a"),
            0x35u);
}

TEST(VirtualInterfaceSim, ClassTaskWaitsOnEdgeThroughProperty) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic clk; endinterface\n"
                      "class drv;\n"
                      "  virtual bus_if vif;\n"
                      "  task run();\n"
                      "    @(posedge vif.clk);\n"
                      "  endtask\n"
                      "endclass\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  drv d;\n"
                      "  integer x;\n"
                      "  initial begin\n"
                      "    x = 0;\n"
                      "    dif.clk = 0;\n"
                      "    d = new;\n"
                      "    d.vif = dif;\n"
                      "    d.run();\n"
                      "    x = $time;\n"
                      "  end\n"
                      "  initial #30 dif.clk = 1;\n"
                      "  initial #200 $finish;\n"
                      "endmodule\n",
                      "top.x"),
            30u);
}

TEST(VirtualInterfaceSim, ClassPropertyInitializedThroughNewArgument) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "class drv;\n"
                      "  virtual bus_if vif;\n"
                      "  function new(virtual bus_if v);\n"
                      "    vif = v;\n"
                      "  endfunction\n"
                      "  function bit [7:0] rd();\n"
                      "    return vif.a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  drv d;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    dif.a = 8'h5C;\n"
                      "    d = new(dif);\n"
                      "    x = d.rd();\n"
                      "  end\n"
                      "endmodule\n",
                      "top.x"),
            0x5Cu);
}

TEST(VirtualInterfaceSim, TaskFormalReceivesInterfaceInstance) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  logic [7:0] x;\n"
                      "  task t(virtual bus_if v);\n"
                      "    x = v.a;\n"
                      "  endtask\n"
                      "  initial begin\n"
                      "    dif.a = 8'h47;\n"
                      "    t(dif);\n"
                      "  end\n"
                      "endmodule\n",
                      "top.x"),
            0x47u);
}

TEST(VirtualInterfaceSim, OutputArgumentWritesClassProperty) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "class drv;\n"
                      "  virtual bus_if vif;\n"
                      "  function bit [7:0] rd();\n"
                      "    return vif.a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  drv d;\n"
                      "  logic [7:0] x;\n"
                      "  function void get(output virtual bus_if v);\n"
                      "    v = dif;\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    dif.a = 8'h63;\n"
                      "    d = new;\n"
                      "    get(d.vif);\n"
                      "    x = d.rd();\n"
                      "  end\n"
                      "endmodule\n",
                      "top.x"),
            0x63u);
}

TEST(VirtualInterfaceSim, OutputArgumentWritesPropertyNamedInsideMethod) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "class db;\n"
                      "  static function void get(output virtual bus_if v,\n"
                      "                           input virtual bus_if src);\n"
                      "    v = src;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class drv;\n"
                      "  virtual bus_if vif;\n"
                      "  function bit [7:0] fetch(virtual bus_if src);\n"
                      "    db::get(vif, src);\n"
                      "    return vif.a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  drv d;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    dif.a = 8'h6E;\n"
                      "    d = new;\n"
                      "    x = d.fetch(dif);\n"
                      "  end\n"
                      "endmodule\n",
                      "top.x"),
            0x6Eu);
}

TEST(VirtualInterfaceSim, PropertyReadBackFromContainerObject) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "class box;\n"
                      "  virtual bus_if v;\n"
                      "endclass\n"
                      "class drv;\n"
                      "  virtual bus_if vif;\n"
                      "  function bit [7:0] rd();\n"
                      "    return vif.a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  box bx;\n"
                      "  drv d;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    dif.a = 8'h7B;\n"
                      "    bx = new;\n"
                      "    bx.v = dif;\n"
                      "    d = new;\n"
                      "    d.vif = bx.v;\n"
                      "    x = d.rd();\n"
                      "  end\n"
                      "endmodule\n",
                      "top.x"),
            0x7Bu);
}

TEST(VirtualInterfaceSim, ClassPropertyComparesWithNullBeforeAndAfterBinding) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "class drv;\n"
                      "  virtual bus_if vif;\n"
                      "  function bit is_null();\n"
                      "    return vif == null;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  drv d;\n"
                      "  bit [1:0] x;\n"
                      "  initial begin\n"
                      "    d = new;\n"
                      "    x[1] = d.is_null();\n"
                      "    d.vif = dif;\n"
                      "    x[0] = d.is_null();\n"
                      "  end\n"
                      "endmodule\n",
                      "top.x"),
            2u);
}

}  // namespace
