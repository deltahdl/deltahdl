// §21.2: Display system tasks


#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(Lowerer, StrobeDoesNotCrash) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x = 42;\n"
      "    $strobe(\"x=%d\", x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

}  // namespace
