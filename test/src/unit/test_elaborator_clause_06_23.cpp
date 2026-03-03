// §6.23: Type operator

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §6.23: type(expr) in variable declaration resolves type.
TEST(SimCh6, TypeRefVarDecl) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 42;\n"
      "    b = 100;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  // type(a) = int → 32-bit width
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 100u);
}

}  // namespace
