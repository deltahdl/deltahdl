#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §25.9: a virtual interface property reaches every component of its
// instance by the dot notation, and §8.11 lets a method name its own property
// through `this`, so `this.vif.a` in a method is the instance's `a`, 0x35.
// Before the base of the access was resolved as an expression, the read took
// `vif.a` for a flat key of the object and answered 0.
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

// §25.9: a nonblocking write through `this.vif` lands on the instance's own
// variable, which the module reads back as `dif.a`; before this the write was
// stored under a flat key of the object and `dif.a` stayed at 0.
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

// §25.9: the module reads a component through the transactor's property by
// the handle it holds, `d.vif.a`, which is the instance's `a`, 0x4A. Before
// this the read followed `d` into the object, took the interface handle held
// in `vif` for a class handle, found no object, and answered 0.
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

// §25.9: a nonblocking write from the module through the transactor's
// property, `d.vif.a <= 8'h5C`, lands on the instance's own variable, read
// back as `dif.a`; before this it was stored under a flat key of the object.
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

// §25.9: the blocking form of the same write reaches the same variable, so
// the module reads its own 0x6D back through `dif.a` in the next statement.
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

// §25.9: an event control on a component reached through the transactor's
// property from the module, `@(posedge d.vif.clk)`, arms on the instance's
// own `clk`, so the block resumes at 30 when another process drives the edge;
// before this the flattened `d.vif.clk` named no variable, nothing was
// armed, and the block sat until the watchdog ended the run with x at 0.
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

// §25.9: the handle chain is followed as deep as the design writes it, so a
// property of an object held by another object, `outer.inner.vif.a`, is the
// instance's `a`, 0x7B, for a read and for a write from the module.
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

// §25.9 and §6.18: a virtual interface declared as a local of a module task,
// through a typedef name standing for the type, is assigned from an instance
// and reaches the instance's `a`, 0x47, through the dot notation. Before this
// the local was a 32-bit vector no reader took for a virtual interface, so
// `v.a` named nothing and x stayed at 0.
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

// §25.9: a write through a module task's local lands on the instance's own
// variable, read back as `dif.a`, 0x58.
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

// §25.9: an event control through a module task's local arms on the
// instance's own `clk`, so the task ends at 30 and the enabling block records
// that time; 0 is what a wait that armed nothing leaves.
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

// §25.9: a virtual interface declared as a local of a class function is
// assigned from another virtual interface, the formal the instance arrived
// through, and reads the instance's `a`, 0x63. A function body's local is
// made on a path of its own (CreateFuncLocalVar), which is why the function
// and the task are each tried.
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

// §25.9: a write through a class task's local lands on the instance's own
// variable, read back as `dif.a`, 0x6E.
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

// §25.9: an event control through a class task's local arms on the
// instance's own `clk`, so the task ends at 30.
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

// §25.9 with A.2.2.1: the local written directly as `virtual bus_if v;`, no
// typedef between, once IsBlockVarDeclStartCore takes `virtual` as opening a
// declaration; it reads the instance's `a`, 0x69, as the typedef form does.
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

}  // namespace
