#include "fixture_simulator.h"
#include "helpers_reported_error.h"

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

}  // namespace
