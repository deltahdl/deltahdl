#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(VirtualInterfaceSim, UnassignedVariableReadsAsNull) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  bit is_null;\n"
      "  initial is_null = (vif == null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("top.is_null");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(VirtualInterfaceSim, AssignNullThenComparePositive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  bit is_null;\n"
      "  initial begin\n"
      "    vif = null;\n"
      "    is_null = (vif == null);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("top.is_null");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(VirtualInterfaceSim, AssignedInstanceNotEqualToNull) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("top.is_null");
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(VirtualInterfaceSim, InitializedComponentReadReflectsInstance) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("top.x");
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

}  // namespace
