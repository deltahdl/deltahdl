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

// §25.9: referencing a component through a virtual interface that is bound to
// no instance is a run-time error, and the reference is what it is about. The
// design holds two references and only the second one goes through an unbound
// virtual interface, so a report carrying no location fails this and so does
// one that names the first reference.
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

// §25.9: attempting to use a null virtual interface shall result in a fatal
// run-time error, and the report names §25.9.
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

// §25.9: "Once a virtual interface has been initialized, all the components of
// the underlying interface instance are directly available to the virtual
// interface via the dot notation. These components can only be used in
// procedural statements". The clause's own example writes a component that way
// with a nonblocking assignment, `bus.req <= 1'b1;`, so the write is a
// redirection through the binding exactly as the read is, and what it must
// reach is the bound instance's own variable.
//
// The claim is read off `u.req`, the instance's signal, rather than back
// through `vif.req`. A read-back through the virtual interface is answered by
// the same redirection the write would have to perform, so it is satisfied by
// a write that landed anywhere that path also looks; `u.req` is only satisfied
// by a write that reached the interface instance.
//
// `u.req` is driven to 1'b0 before the binding, so the two outcomes are
// distinct values and not a value against x: the run reads 1'b1 when the
// nonblocking write reached the instance and 1'b0 when it was dropped. The #1
// is what makes the read an observation of the write at all -- §10.4.2 has a
// nonblocking assignment update in the NBA region of the current time step, so
// a read placed in the same statement sequence at time 0 sees the old value
// however the write behaves.
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

// §25.9: the same rule under a blocking assignment. The clause grants the
// components of the underlying instance to procedural statements without
// distinguishing the two assignment forms, so `vh.data = 8'hC3;` must reach
// the instance as the nonblocking form above must.
//
// The component is a vector rather than a bit, and the value 8'hC3 has bits
// set in both nibbles, so a write that reached the instance only partially --
// one bit of it, or a truncation to the 1-bit component the case above uses --
// is a different reading from the whole 0xC3 and fails.
//
// The observation is made on the context variable the run left behind rather
// than through a second procedural read: `top.dut.data` IS the interface
// instance's variable, so nothing at all stands between the write and the
// claim. The read of `vh.data` into `echo` is a separate claim, and not the
// one that catches a dropped write -- it says the read redirect of §25.9 is
// still in force over a component the write has just touched, and it would be
// satisfied by a write that never reached `dut`.
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

// §25.9 makes a component available through the virtual interface only "once a
// virtual interface has been initialized", and the file's cases above hold the
// simulator to reporting a read that is not: a reference through an unbound
// handle is a fatal run-time error carrying §25.9. A write names the component
// by the same dot notation and through the same absent binding, so it is the
// same violation, and a run that drops the write in silence reports nothing
// where the read reports.
//
// Two writes stand in the design and only the second one goes through an
// unbound handle, so a report carrying no location fails this and so does one
// that names the write through `held`. Line 12 is `dropped.q = 1'b1;`.
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

// §25.9: once a virtual interface variable is initialized, every component of
// the interface instance it represents is reached through it by the dot
// notation, and the clause's own transactor waits on a posedge of one that
// way. §9.4.2 then detects the posedge on the instance's variable as on any
// other. The process resumes at the edge, so `x` records 30, the time of the
// 0-to-1 transition. Recording 10 would mean the negedge at 10 resumed it, a
// level wait rather than a posedge one; 0 that nothing resumed it before the
// watchdog ended the run, which is what an event control that resolved `v.clk`
// to nothing did.
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

// §9.4.2: a non-edge implicit event is detected on any change of the
// expression, so `@(v.clk)` resumes on the 1-to-0 transition at 20, which a
// posedge wait would let pass; 60, the later posedge, is what such a wait
// would record, and 0 what an unarmed one leaves.
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

// §9.4.2: every operand of an `or` list is watched, so a change on `v.b`
// alone resumes the process at 35. Recording 70, when `v.a` changes, would
// mean only the first operand reached the instance.
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

// §9.4.2: a change in an operand of the expression without a change in its
// result is not an event, so `@(v.a & v.b)` lets the change of `v.a` at 15
// pass and resumes when `v.b` makes the conjunction 1 at 40. Recording 15
// would mean the operands were watched as two bare names rather than as the
// one expression; 0 that the names were collected from the handle rather
// than from the instance and nothing resumed the process.
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

// §25.9: an event control names a component through the virtual interface
// exactly as a read does, so waiting on one through an unbound variable is
// the same fatal run-time error a read through it is, reported at the wait
// rather than left as a process that nothing will ever resume. Line 7 is the
// `@(posedge v.clk);`.
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

// §25.9: the same violation in a compound operand. The operands of
// `v.a & v.b` are reached through an unbound variable, and the expression is
// evaluated when the wait arms whatever names it yields to watch, so the
// error is reported at line 6, the `@(v.a & v.b);`, whether or not any
// watcher was armed.
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

// §25.9: a virtual interface can be declared as a class property, and once it
// is initialized every component of the instance it represents is reached
// through it by the dot notation. The module binds the property from outside,
// `d.vif = dif`, and the method reads `vif.a` by the property's bare name; the
// read reaches the instance's own `a`, which the module wrote 0x35 into. A
// property bound to nothing reports a null reference and reads 0.
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

// §25.9: the clause's own transactor writes `bus.req <= 1'b1` through its
// property. A nonblocking write through the property lands on the instance's
// own variable, which the module reads back by its hierarchical name; an
// unbound property would leave `dif.a` at its uninitialized value.
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

// §25.9: the transactor's wait_for_bus waits on `@(posedge bus.grant)` with
// `bus` a property. The event control arms on the instance's own `clk`, so the
// task ends at 30, when another process drives the edge, and the enabling
// process records that time; 0 is what a wait that armed nothing would leave,
// the watchdog ending the run.
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

// §25.9: a virtual interface property can be initialized by an argument to
// new(), which is how the clause's SBusTransactor is built, `bus = s` in its
// constructor. The instance passed to new() is what the property represents
// afterwards, so the read through it answers the instance's 0x5C.
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

// §25.9: a virtual interface may be passed as an argument to a task. The
// formal is a virtual interface of its own, so `v.a` in the body is the
// component of the instance the call passed, 0x47.
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

// §25.9 and §13.5.2: an output formal declared `virtual bus_if` is copied to
// its actual when the function returns, and the actual is a class property
// named from the module, `get(d.vif)`. The property then represents the
// instance the function assigned, and a read through it answers 0x63.
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

// §25.9 and §13.5.2, the copy-out reaching a property named by its bare name:
// a method of the class passes its own property as the actual of a static
// method of another class, `db::get(vif, src)`, which is how a component asks
// a resource database for its interface, and the instance arrives through the
// method's own virtual interface formal. The copy-out writes the property of
// the object the method runs on, against that object's class rather than the
// database's, and the read that follows it in the same method answers the
// instance's 0x6E.
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

// §25.9: a virtual interface is assigned from another virtual interface, so
// one held as a property of a container object, `bx.v`, is read back and
// assigned to the transactor's own property, which then represents the same
// instance and reads its 0x7B.
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

// §25.9: a virtual interface property has the value null before it is
// initialized and compares equal to null then, and unequal once it represents
// an instance. The two comparisons are packed as {before, after}, so 2 is the
// answer; 3 would mean the binding was not seen, 0 that the null state was
// not.
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
