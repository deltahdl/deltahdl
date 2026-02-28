// §6.20: Constants


#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §6.20.5: Specparam values accessible during simulation.
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

}  // namespace
