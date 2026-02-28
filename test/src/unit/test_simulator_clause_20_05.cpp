// §20.5: Conversion functions

#include <cstring>

#include "parser/ast.h"
#include "simulator/eval.h"

#include "fixture_simulator.h"
#include "builders_systask.h"

using namespace delta;

namespace {

TEST(SysTask, ItoRConvertsIntToReal) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$itor", {MkInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 64u);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 42.0);
}

TEST(SysTask, RtoIConvertsRealToInt) {
  SysTaskFixture f;
  double dval = 3.7;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  auto* real_arg = f.arena.Create<Expr>();
  real_arg->kind = ExprKind::kRealLiteral;
  real_arg->real_val = dval;
  auto* expr = MkSysCall(f.arena, "$rtoi", {real_arg});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(SysTask, BitstorealReinterpretsBitsAsReal) {
  SysTaskFixture f;
  double expected = 42.0;
  uint64_t bits = 0;
  std::memcpy(&bits, &expected, sizeof(double));
  auto* expr = MkSysCall(f.arena, "$bitstoreal", {MkInt(f.arena, bits)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 64u);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 42.0);
}

TEST(SysTask, RealtobitsReinterpretsRealAsBits) {
  SysTaskFixture f;
  double dval = 42.0;
  auto* real_arg = f.arena.Create<Expr>();
  real_arg->kind = ExprKind::kRealLiteral;
  real_arg->real_val = dval;
  auto* expr = MkSysCall(f.arena, "$realtobits", {real_arg});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 64u);
  uint64_t expected_bits = 0;
  std::memcpy(&expected_bits, &dval, sizeof(double));
  EXPECT_EQ(result.ToUint64(), expected_bits);
}

// § system_tf_call — $unsigned
TEST(SimA82, SystemTfCallUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = $unsigned(8'sd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

}  // namespace
