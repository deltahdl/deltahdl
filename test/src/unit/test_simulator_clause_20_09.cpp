// §20.9: Bit vector system functions

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(SysTask, CountbitsMatchingPattern) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$countbits",
                         {MkInt(f.arena, 0xA5), MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 4u);
}

// ============================================================================
// §20.9 — $countones, $onehot, $onehot0, $isunknown
// ============================================================================
TEST(Section20, CountonesZero) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$countones", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, CountonesAllBits) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$countones", {MakeInt(f.arena, 0xFF)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 8u);
}

TEST(Section20, CountonesSparse) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$countones", {MakeInt(f.arena, 0b10101)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(Section20, OnehotTrue) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot", {MakeInt(f.arena, 4)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, OnehotFalseZero) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
