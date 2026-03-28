#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(Lowerer, SpecparamValue) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  specparam DELAY = 42;\n"
      "  int result;\n"
      "  initial result = DELAY;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// "Constants are named data objects" — parameter value readable at runtime.
TEST(Lowerer, ParameterValueAccessibleAtRuntime) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int WIDTH = 16;\n"
      "  int result;\n"
      "  initial result = WIDTH;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(Lowerer, LocalparamValueAccessibleAtRuntime) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int DEPTH = 64;\n"
      "  int result;\n"
      "  initial result = DEPTH;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 64u);
}

}  // namespace
