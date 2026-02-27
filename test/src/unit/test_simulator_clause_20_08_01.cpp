// §20.8.1: Integer math functions


#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// § system_tf_call — $clog2 returns computed value
TEST(SimA82, SystemTfCallClog2) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = $clog2(256);\n"
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

// § primary — system call ($clog2)
TEST(SimA84, PrimarySystemCallClog2) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial x = $clog2(16);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

}  // namespace
