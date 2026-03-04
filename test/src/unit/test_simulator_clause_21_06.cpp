#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/eval.h"

using namespace delta;
namespace {

TEST(Section20, TestPlusargsNotFound) {
  SimFixture f;
  auto* expr =
      MakeSysCall(f.arena, "$test$plusargs", {MkStr(f.arena, "VERBOSE")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, TestPlusargsFound) {
  SimFixture f;
  f.ctx.AddPlusArg("VERBOSE");
  auto* expr =
      MakeSysCall(f.arena, "$test$plusargs", {MkStr(f.arena, "VERBOSE")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, TestPlusargsPrefixMatch) {
  SimFixture f;
  f.ctx.AddPlusArg("VERBOSE=1");
  auto* expr = MakeSysCall(f.arena, "$test$plusargs", {MkStr(f.arena, "VERB")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, ValuePlusargsFound) {
  SimFixture f;
  f.ctx.AddPlusArg("DEPTH=42");
  auto* dest_var = f.ctx.CreateVariable("depth", 32);
  dest_var->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* expr =
      MakeSysCall(f.arena, "$value$plusargs",
                  {MkStr(f.arena, "DEPTH=%d"), MakeId(f.arena, "depth")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(dest_var->value.ToUint64(), 42u);
}

TEST(Section20, ValuePlusargsNotFound) {
  SimFixture f;
  auto* dest_var = f.ctx.CreateVariable("depth", 32);
  dest_var->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* expr =
      MakeSysCall(f.arena, "$value$plusargs",
                  {MkStr(f.arena, "DEPTH=%d"), MakeId(f.arena, "depth")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
