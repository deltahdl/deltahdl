#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(InitialProcedureSimulation, InitialBlockSchedulesEvent) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_TRUE(f.scheduler.HasEvents());
}

TEST(InitialProcedureSimulation, InitialBlockExecutes) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(InitialProcedureSimulation, NoSensitivityRegistered) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  const auto& procs = f.ctx.GetSensitiveProcesses("x");
  EXPECT_TRUE(procs.empty());
}

TEST(InitialProcedureSimulation, ParallelInitialBlocksBothComplete) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = 8'd42;\n"
      "  initial b = 8'd99;\n"
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
  EXPECT_EQ(va->value.ToUint64(), 42u);
  EXPECT_EQ(vb->value.ToUint64(), 99u);
}

TEST(InitialProcedureSimulation, EmptyInitialDoesNotInterfere) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin end\n"
      "  initial a = 8'd77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 77u);
}

TEST(InitialProcedureSimulation, FiveParallelInitialBlocks) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d, e;\n"
      "  initial a = 8'd1;\n"
      "  initial b = 8'd2;\n"
      "  initial c = 8'd3;\n"
      "  initial d = 8'd4;\n"
      "  initial e = 8'd5;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"a", 1u}, {"b", 2u}, {"c", 3u}, {"d", 4u}, {"e", 5u}});
}

TEST(InitialProcedureSimulation, SequentialBlockingAssignmentsAtTimeZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = a + 8'd1;\n"
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
  EXPECT_EQ(va->value.ToUint64(), 1u);
  EXPECT_EQ(vb->value.ToUint64(), 2u);
}

TEST(InitialProcedureSimulation, InitialCeasesWhenStatementFinishes) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x = 1;\n"
      "    x = x + 1;\n"
      "    x = x + 1;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 3u);
}

TEST(InitialProcedureSimulation, ExecutesExactlyOnce) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    count = count + 1;\n"
      "  end\n"
      "endmodule\n",
      "count");
  EXPECT_EQ(val, 1u);
}

TEST(InitialProcedureSimulation, InitialWithDelayCeases) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    #5 x = 42;\n"
      "  end\n"
      "  initial #10 $finish;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

TEST(InitialProcedureSimulation, NullStatementInitialCompletes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial ;\n"
      "  initial x = 8'd55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 55u);
}

}  // namespace
