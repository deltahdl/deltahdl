#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

  EXPECT_EQ(var->value.ToUint64(), 3u);
}

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

  auto neg2_32bit = static_cast<uint32_t>(-2);
  EXPECT_EQ(var->value.ToUint64(), neg2_32bit);
}

TEST(SimCh6, CastRealToInt_Truncate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int result;\n"
      "  initial begin\n"
      "    r = 2.4;\n"
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

  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §6.12.1 LRM examples: 35.7 and 35.5 both become 36, 35.2 becomes 35.
TEST(SimCh6, CastRealToInt_LrmExamples) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r1, r2, r3;\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    r1 = 35.7; a = int'(r1);\n"
      "    r2 = 35.5; b = int'(r2);\n"
      "    r3 = 35.2; c = int'(r3);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 36u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 36u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 35u);
}

// §6.12.1 LRM example: 1.5 to integer yields 2.
TEST(SimCh6, CastRealToInt_PosHalfRoundsAway) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int result;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    result = int'(r);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 2u);
}

}  // namespace
