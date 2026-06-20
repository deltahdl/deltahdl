#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(SysTask, CountbitsMatchingPattern) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$countbits",
                         {MkInt(f.arena, 0xA5), MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 4u);
}

TEST(UtilitySystemTaskTest, CountonesZero) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$countones", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(UtilitySystemTaskTest, CountonesAllBits) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$countones", {MakeInt(f.arena, 0xFF)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 8u);
}

TEST(UtilitySystemTaskTest, CountonesSparse) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$countones", {MakeInt(f.arena, 0b10101)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(UtilitySystemTaskTest, OnehotTrue) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot", {MakeInt(f.arena, 4)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(UtilitySystemTaskTest, OnehotFalseZero) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(UtilitySystemTaskTest, OnehotFalseMultiple) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot", {MakeInt(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(UtilitySystemTaskTest, Onehot0True) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot0", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(UtilitySystemTaskTest, Onehot0TrueOneBit) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot0", {MakeInt(f.arena, 8)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(UtilitySystemTaskTest, Onehot0FalseMultiple) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot0", {MakeInt(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(UtilitySystemTaskTest, IsunknownFalse) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$isunknown", {MakeInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(UtilitySystemTaskTest, IsunknownTrueXVar) {
  SimFixture f;

  f.ctx.CreateVariable("xvar", 8);
  auto* expr = MakeSysCall(f.arena, "$isunknown", {MakeId(f.arena, "xvar")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §20.9: a wider control_bit is reduced to its low bit before matching. Here
// 0xE has LSB 0, so the call counts the zero bits of the 32-bit operand
// 0x000000A5 -> 32 - popcount(0xA5) = 28.
TEST(UtilitySystemTaskTest, CountbitsControlBitOnlyLsbUsed) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$countbits",
                         {MkInt(f.arena, 0xA5), MkInt(f.arena, 0xE)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 28u);
}

// §20.9: a control_bit value repeated in the argument list contributes the
// same as a single occurrence, so calling with '1 twice yields the same
// result as calling with '1 once.
TEST(UtilitySystemTaskTest, CountbitsControlBitDeduplicated) {
  SysTaskFixture f;
  auto* once = MkSysCall(f.arena, "$countbits",
                         {MkInt(f.arena, 0xA5), MkInt(f.arena, 1)});
  auto* twice =
      MkSysCall(f.arena, "$countbits",
                {MkInt(f.arena, 0xA5), MkInt(f.arena, 1), MkInt(f.arena, 1)});
  auto r_once = EvalExpr(once, f.ctx, f.arena);
  auto r_twice = EvalExpr(twice, f.ctx, f.arena);
  EXPECT_EQ(r_once.ToUint64(), r_twice.ToUint64());
  EXPECT_EQ(r_twice.ToUint64(), 4u);
}

// §20.9: the control_bit may be a variable, not a constant. The simulator
// must evaluate the control_bit expression at call time and use its LSB.
// Here ctrl is a 1-bit variable holding 1, so the call counts the four 1-bits
// of 0xA5.
TEST(UtilitySystemTaskTest, CountbitsVariableControlBitAtRuntime) {
  SysTaskFixture f;
  MakeVar(f, "ctrl", 1, 1);
  auto* expr = MakeSysCall(f.arena, "$countbits",
                           {MakeInt(f.arena, 0xA5), MakeId(f.arena, "ctrl")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 4u);
}

// §20.9: $countones is equivalent to $countbits(expression, '1), so x/z bits
// in the expression must not be counted. Build an 8-bit value whose bit 0 is
// 1 and whose upper nibble is x; only the single known 1-bit must register.
TEST(UtilitySystemTaskTest, CountonesIgnoresUnknownBits) {
  SysTaskFixture f;
  auto* var = f.ctx.CreateVariable("mix", 8);
  var->value.words[0].aval = 0x01;
  var->value.words[0].bval = 0xF0;
  auto* expr = MakeSysCall(f.arena, "$countones", {MakeId(f.arena, "mix")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §20.9: $isunknown is true when $countbits(expression, 'x, 'z) is non-zero,
// so z-only operands must register as unknown just like x-only operands do.
// Convert the default-x variable bits into z by also setting aval, leaving
// bval set.
TEST(UtilitySystemTaskTest, IsunknownTrueZVar) {
  SysTaskFixture f;
  auto* var = f.ctx.CreateVariable("zvar", 8);
  for (uint32_t i = 0; i < var->value.nwords; ++i) {
    var->value.words[i].aval = ~uint64_t{0};
  }
  auto* expr = MakeSysCall(f.arena, "$isunknown", {MakeId(f.arena, "zvar")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

}  // namespace
