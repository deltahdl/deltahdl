// §20.6.2: Expression size system function

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// § primary — system call ($bits)
TEST(SimA84, PrimarySystemCallBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  int x;\n"
      "  initial x = $bits(data);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

TEST(Section20, BitsOfVariable) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("wide_var", 64);
  var->value = MakeLogic4VecVal(f.arena, 64, 0);
  auto* expr = MakeSysCall(f.arena, "$bits", {MakeId(f.arena, "wide_var")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 64u);
}

}  // namespace
