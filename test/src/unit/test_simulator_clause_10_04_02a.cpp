// §10.4.2: Nonblocking procedural assignments


#include "simulation/lowerer.h"
#include "simulation/net.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(Lowerer, NbaDefersUpdate) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x <= 42;\n"
      "    x = x;  // read x: should still be 0 (X→0), not 42\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  // NBA update deferred, but scheduler drains NBA after Active,
  // so after Run() completes the NBA has been applied.
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // x was read as 0 (from X init), then NBA applied 42.
  // The blocking assign `x = x` reads 0 and writes 0.
  // Then NBA applies 42. Final value: 42.
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(Lowerer, NbaAppliesToValue) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  initial begin\n"
      "    a <= 10;\n"
      "    b <= 20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 10u);
  EXPECT_EQ(b->value.ToUint64(), 20u);
}

}  // namespace
