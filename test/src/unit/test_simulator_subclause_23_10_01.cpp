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

// A defparam over a string parameter declared as a module item, which is the
// one shape where Elaborator::ElaborateParamDecl has already recorded the
// declaration's own characters in RtlirParamDecl::resolved_string by the time
// the defparam replaces resolved_value. Lowerer::LowerParams reads
// resolved_string for a string parameter, so a lowering that read it here
// would run the design with "abc" -- the value the defparam overrode -- and
// report nothing.
TEST(DefparamSimulation, OverriddenStringParameterVisibleAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  parameter string P = \"abc\";\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "  defparam u.P = \"xyz\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("u.P");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(Logic4VecToString(var->value), "xyz");
}

}  // namespace
