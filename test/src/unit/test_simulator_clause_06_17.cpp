// §6.17: Event data type

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(Lowerer, EventVariableCreated) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("ev");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_event);
}

}  // namespace
