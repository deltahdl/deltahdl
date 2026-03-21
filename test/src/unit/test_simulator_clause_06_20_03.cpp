#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TypeParameterSim, DefaultTypeParamResolvesWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter type T = shortint;\n"
      "  T x;\n"
      "  initial x = 32'hFFFFFFFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFu);
}

TEST(TypeParameterSim, LocalparamTypeResolvesWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam type T = byte;\n"
      "  T data;\n"
      "  initial data = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("data");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(TypeParameterSim, MultipleTypeParamsResolveCorrectly) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter type A = int;\n"
      "  parameter type B = shortint;\n"
      "  A x;\n"
      "  B y;\n"
      "  initial begin\n"
      "    x = 32'hDEADBEEF;\n"
      "    y = 16'hCAFE;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* vx = f.ctx.FindVariable("x");
  auto* vy = f.ctx.FindVariable("y");
  ASSERT_NE(vx, nullptr);
  ASSERT_NE(vy, nullptr);

  EXPECT_EQ(vx->value.width, 32u);
  EXPECT_EQ(vx->value.ToUint64(), 0xDEADBEEFu);
  EXPECT_EQ(vy->value.width, 16u);
  EXPECT_EQ(vy->value.ToUint64(), 0xCAFEu);
}

}  // namespace
