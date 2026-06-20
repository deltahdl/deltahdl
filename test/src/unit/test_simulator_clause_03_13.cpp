#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(NameSpaceSimulation, PackageNameSpaceValueAtRuntime) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  parameter int V = 7;\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::V;\n"
      "  logic [31:0] y;\n"
      "  initial y = V;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 7u);
}

TEST(NameSpaceSimulation, ModuleNameSpaceInstanceAddressableAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic [7:0] v;\n"
      "  initial v = 8'h55;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    #1;\n"
      "    r = c1.v;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0x55u);
}

TEST(NameSpaceSimulation, BlockNameSpaceIsolatesLocalVariables) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] r1, r2;\n"
      "  initial begin : b1\n"
      "    int x;\n"
      "    x = 1;\n"
      "    r1 = x;\n"
      "  end\n"
      "  initial begin : b2\n"
      "    int x;\n"
      "    x = 2;\n"
      "    r2 = x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v1 = f.ctx.FindVariable("r1");
  auto* v2 = f.ctx.FindVariable("r2");
  ASSERT_NE(v1, nullptr);
  ASSERT_NE(v2, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 1u);
  EXPECT_EQ(v2->value.ToUint64(), 2u);
}

}  // namespace
