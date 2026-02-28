// §9.4.3: Level-sensitive event control


#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(Lowerer, WaitConditionTrue) {
  // wait(expr) when condition is immediately true.
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x = 1;\n"
      "    wait (x) x = 42;\n"
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

TEST(Lowerer, WaitConditionDeferred) {
  // wait(expr) when condition is initially false, becomes true later.
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] flag, result;\n"
      "  initial begin\n"
      "    flag = 0;\n"
      "    #5 flag = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (flag) result = 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

}  // namespace
