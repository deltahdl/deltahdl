#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(DefparamSimulation, OverriddenParameterVisibleAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int VAL = 1) ();\n"
      "  int observed;\n"
      "  initial observed = VAL;\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "  defparam u.VAL = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(DefparamSimulation, LastDefparamVisibleAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int VAL = 1) ();\n"
      "  int observed;\n"
      "  initial observed = VAL;\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "  defparam u.VAL = 10;\n"
      "  defparam u.VAL = 20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

}  // namespace
