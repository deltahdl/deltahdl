#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(Lowerer, InitialBlockSchedulesEvent) {
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

TEST(Lowerer, InitialBlockExecutes) {
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

TEST(Lowerer, SensitivityMapEmpty) {
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

TEST(SimCh4, ParallelInitialBlocks) {
  auto a = RunAndGet(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = 8'd42;\n"
      "  initial b = 8'd99;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(a, 42u);
}

TEST(SimCh4, ParallelInitialBlocksBothComplete) {
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

TEST(SimCh4, EmptyProcessNoInterference) {
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

TEST(SimCh4, FiveParallelInitialBlocks) {
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

}  // namespace
