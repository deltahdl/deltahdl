// §20.6.3: Range system function

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §6.20.7: $isunbounded returns 1 for parameter with $ value.
TEST(SimCh6, IsunboundedTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int p = $;\n"
      "  int result;\n"
      "  initial result = $isunbounded(p);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §6.20.7: $isunbounded returns 0 for parameter with numeric value.
TEST(SimCh6, IsunboundedFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int p = 42;\n"
      "  int result;\n"
      "  initial result = $isunbounded(p);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

}  // namespace
