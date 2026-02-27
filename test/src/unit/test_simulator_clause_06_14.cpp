// §6.14: Chandle data type


#include "simulation/lowerer.h"
#include "simulation/net.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §6.14: Chandle variables initialized to null, boolean test.
TEST(Lowerer, ChandleNullDefault) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    if (h == null) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
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

}  // namespace
