// §6.12.1: Conversion

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §6.12.1: real→int cast rounds to nearest, ties away from zero.
TEST(SimCh6, CastRealToInt_RoundUp) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int result;\n"
      "  initial begin\n"
      "    r = 2.5;\n"
      "    result = int'(r);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // 2.5 rounds to 3 (ties away from zero).
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// §6.12.1: real→int cast rounds negative half away from zero.
TEST(SimCh6, CastRealToInt_NegRound) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int result;\n"
      "  initial begin\n"
      "    r = -1.5;\n"
      "    result = int'(r);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // -1.5 rounds to -2 (ties away from zero). As uint64: 0xFFFFFFFE.
  auto neg2_32bit = static_cast<uint32_t>(-2);
  EXPECT_EQ(var->value.ToUint64(), neg2_32bit);
}

}  // namespace
