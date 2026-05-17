#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §23.10.1: "Using the defparam statement, parameter values can be changed
// in any module, interface, or program instance throughout the design using
// the hierarchical name of the parameter." The override applied at
// elaboration time shall be the value read at simulation time.
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

// §23.10.1: "In the case of multiple defparams for a single parameter, the
// parameter takes the value of the last defparam statement encountered in
// the source text." The last-wins value shall be the one observed at
// simulation time.
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
