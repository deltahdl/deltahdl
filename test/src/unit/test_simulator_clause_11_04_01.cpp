// §11.4.1: Assignment operators


#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// § variable_lvalue — compound assignment +=
TEST(SimA85, VarLvalueCompoundAdd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial begin x = 10; x += 5; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

}  // namespace
