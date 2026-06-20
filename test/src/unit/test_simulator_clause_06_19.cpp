#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(EnumerationSimulation, DefaultIntBaseTypeWidthAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  enum {IDLE, BUSY, DONE} state;\n"
      "  int observed;\n"
      "  initial begin\n"
      "    state = BUSY;\n"
      "    observed = state;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("state");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
}

TEST(EnumerationSimulation, AutoIncrementedValuesPropagateAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {ZERO, ONE, TWO} count_t;\n"
      "  int observed;\n"
      "  initial begin\n"
      "    observed = TWO;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

}  // namespace
