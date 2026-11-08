#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(VirtualInterfaceSim, ThisQualifiedPropertyReadsInstanceComponent) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "class drv;\n"
                      "  virtual bus_if vif;\n"
                      "  function bit [7:0] rd();\n"
                      "    return this.vif.a;\n"
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

TEST(VirtualInterfaceSim, ThisQualifiedPropertyWriteReachesInstance) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "class drv;\n"
                      "  virtual bus_if vif;\n"
                      "  task run();\n"
                      "    this.vif.a <= 8'h2C;\n"
                      "  endtask\n"
                      "endclass\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  drv d;\n"
                      "  initial begin\n"
                      "    dif.a = 0;\n"
                      "    d = new;\n"
                      "    d.vif = dif;\n"
                      "    d.run();\n"
                      "  end\n"
                      "endmodule\n",
                      "top.dif.a"),
            0x2Cu);
}

TEST(VirtualInterfaceSim, PropertyReadThroughHandleFromModule) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "class drv;\n"
                      "  virtual bus_if vif;\n"
                      "endclass\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  drv d;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    dif.a = 8'h4A;\n"
                      "    d = new;\n"
                      "    d.vif = dif;\n"
                      "    x = d.vif.a;\n"
                      "  end\n"
                      "endmodule\n",
                      "top.x"),
            0x4Au);
}

TEST(VirtualInterfaceSim, NonblockingWriteThroughHandleFromModule) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "class drv;\n"
                      "  virtual bus_if vif;\n"
                      "endclass\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  drv d;\n"
                      "  initial begin\n"
                      "    dif.a = 0;\n"
                      "    d = new;\n"
                      "    d.vif = dif;\n"
                      "    d.vif.a <= 8'h5C;\n"
                      "  end\n"
                      "endmodule\n",
                      "top.dif.a"),
            0x5Cu);
}

TEST(VirtualInterfaceSim, BlockingWriteThroughHandleFromModule) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "class drv;\n"
                      "  virtual bus_if vif;\n"
                      "endclass\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  drv d;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    dif.a = 0;\n"
                      "    d = new;\n"
                      "    d.vif = dif;\n"
                      "    d.vif.a = 8'h6D;\n"
                      "    x = dif.a;\n"
                      "  end\n"
                      "endmodule\n",
                      "top.x"),
            0x6Du);
}

TEST(VirtualInterfaceSim, EventControlThroughHandleFromModule) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic clk; endinterface\n"
                      "class drv;\n"
                      "  virtual bus_if vif;\n"
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
                      "    @(posedge d.vif.clk);\n"
                      "    x = $time;\n"
                      "  end\n"
                      "  initial #30 dif.clk = 1;\n"
                      "  initial #200 $finish;\n"
                      "endmodule\n",
                      "top.x"),
            30u);
}

TEST(VirtualInterfaceSim, TwoLevelHandleChainReachesInstanceComponent) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "class inner_t;\n"
                      "  virtual bus_if vif;\n"
                      "endclass\n"
                      "class outer_t;\n"
                      "  inner_t inner;\n"
                      "  function new();\n"
                      "    inner = new;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  outer_t outer;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    dif.a = 8'h7B;\n"
                      "    outer = new;\n"
                      "    outer.inner.vif = dif;\n"
                      "    x = outer.inner.vif.a;\n"
                      "  end\n"
                      "endmodule\n",
                      "top.x"),
            0x7Bu);
}

TEST(VirtualInterfaceSim, TwoLevelHandleChainWriteReachesInstance) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "class inner_t;\n"
                      "  virtual bus_if vif;\n"
                      "endclass\n"
                      "class outer_t;\n"
                      "  inner_t inner;\n"
                      "  function new();\n"
                      "    inner = new;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  outer_t outer;\n"
                      "  initial begin\n"
                      "    dif.a = 0;\n"
                      "    outer = new;\n"
                      "    outer.inner.vif = dif;\n"
                      "    outer.inner.vif.a <= 8'h3E;\n"
                      "  end\n"
                      "endmodule\n",
                      "top.dif.a"),
            0x3Eu);
}

TEST(VirtualInterfaceSim, ModuleTaskLocalReadsInstanceComponent) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "module top;\n"
                      "  typedef virtual bus_if vif_t;\n"
                      "  bus_if dif();\n"
                      "  logic [7:0] x;\n"
                      "  task t();\n"
                      "    vif_t v;\n"
                      "    v = dif;\n"
                      "    x = v.a;\n"
                      "  endtask\n"
                      "  initial begin\n"
                      "    dif.a = 8'h47;\n"
                      "    t();\n"
                      "  end\n"
                      "endmodule\n",
                      "top.x"),
            0x47u);
}

TEST(VirtualInterfaceSim, ModuleTaskLocalWriteReachesInstance) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "module top;\n"
                      "  typedef virtual bus_if vif_t;\n"
                      "  bus_if dif();\n"
                      "  task t();\n"
                      "    vif_t v;\n"
                      "    v = dif;\n"
                      "    v.a <= 8'h58;\n"
                      "  endtask\n"
                      "  initial begin\n"
                      "    dif.a = 0;\n"
                      "    t();\n"
                      "  end\n"
                      "endmodule\n",
                      "top.dif.a"),
            0x58u);
}

TEST(VirtualInterfaceSim, ModuleTaskLocalWaitsOnInstanceEdge) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic clk; endinterface\n"
                      "module top;\n"
                      "  typedef virtual bus_if vif_t;\n"
                      "  bus_if dif();\n"
                      "  integer x;\n"
                      "  task t();\n"
                      "    vif_t v;\n"
                      "    v = dif;\n"
                      "    @(posedge v.clk);\n"
                      "  endtask\n"
                      "  initial begin\n"
                      "    x = 0;\n"
                      "    dif.clk = 0;\n"
                      "    t();\n"
                      "    x = $time;\n"
                      "  end\n"
                      "  initial #30 dif.clk = 1;\n"
                      "  initial #200 $finish;\n"
                      "endmodule\n",
                      "top.x"),
            30u);
}

TEST(VirtualInterfaceSim, ClassFunctionLocalReadsInstanceComponent) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "typedef virtual bus_if vif_t;\n"
                      "class drv;\n"
                      "  function bit [7:0] rd(virtual bus_if src);\n"
                      "    vif_t v;\n"
                      "    v = src;\n"
                      "    return v.a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  drv d;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    dif.a = 8'h63;\n"
                      "    d = new;\n"
                      "    x = d.rd(dif);\n"
                      "  end\n"
                      "endmodule\n",
                      "top.x"),
            0x63u);
}

TEST(VirtualInterfaceSim, ClassTaskLocalWriteReachesInstance) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "typedef virtual bus_if vif_t;\n"
                      "class drv;\n"
                      "  task run(virtual bus_if src);\n"
                      "    vif_t v;\n"
                      "    v = src;\n"
                      "    v.a <= 8'h6E;\n"
                      "  endtask\n"
                      "endclass\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  drv d;\n"
                      "  initial begin\n"
                      "    dif.a = 0;\n"
                      "    d = new;\n"
                      "    d.run(dif);\n"
                      "  end\n"
                      "endmodule\n",
                      "top.dif.a"),
            0x6Eu);
}

TEST(VirtualInterfaceSim, ClassTaskLocalWaitsOnInstanceEdge) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic clk; endinterface\n"
                      "typedef virtual bus_if vif_t;\n"
                      "class drv;\n"
                      "  task run(virtual bus_if src);\n"
                      "    vif_t v;\n"
                      "    v = src;\n"
                      "    @(posedge v.clk);\n"
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
                      "    d.run(dif);\n"
                      "    x = $time;\n"
                      "  end\n"
                      "  initial #30 dif.clk = 1;\n"
                      "  initial #200 $finish;\n"
                      "endmodule\n",
                      "top.x"),
            30u);
}

TEST(VirtualInterfaceSim, ModuleTaskDirectLocalReadsInstanceComponent) {
  EXPECT_EQ(RunAndGet("interface bus_if; logic [7:0] a; endinterface\n"
                      "module top;\n"
                      "  bus_if dif();\n"
                      "  logic [7:0] x;\n"
                      "  task t();\n"
                      "    virtual bus_if v;\n"
                      "    v = dif;\n"
                      "    x = v.a;\n"
                      "  endtask\n"
                      "  initial begin\n"
                      "    dif.a = 8'h69;\n"
                      "    t();\n"
                      "  end\n"
                      "endmodule\n",
                      "top.x"),
            0x69u);
}

TEST(VirtualInterfaceSim, AMemberReadThroughTheHandleKeepsItsSignedness) {
  SimFixture f;
  std::string out = RunCapture(
      "interface SBus; logic a; endinterface\n"
      "module top;\n"
      "  SBus s();\n"
      "  virtual SBus v;\n"
      "  initial begin\n"
      "    v = s; s.a = 1;\n"
      "    #1 $display(\"%0d %0d %0d\", s.a, v.a, v.a + 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1\n");
}

TEST(VirtualInterfaceSim, NestedInterfaceInstanceIsReached) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface inner_if; int v; endinterface\n"
                       "interface outer_if;\n"
                       "  inner_if in();\n"
                       "endinterface\n"
                       "module top;\n"
                       "  outer_if o();\n"
                       "  virtual outer_if vo;\n"
                       "  initial begin\n"
                       "    vo = o;\n"
                       "    vo.in.v = 5;\n"
                       "    $display(\"inner=%0d\", o.in.v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "inner=5\n");
}

}  // namespace
