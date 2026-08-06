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
  // observed is declared in child, instantiated as u, so its runtime storage is
  // u.observed; query the hierarchical name (the scheduler leaves no current
  // process installed once it goes idle, so a bare name resolves in top scope).
  auto* var = f.ctx.FindVariable("u.observed");
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
  // observed lives in child instance u; query u.observed (no current process is
  // installed once the scheduler is idle, so a bare name resolves in top
  // scope).
  auto* var = f.ctx.FindVariable("u.observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

}  // namespace
