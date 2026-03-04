#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/eval.h"

using namespace delta;
namespace {

TEST(Section21, SscanfDecimal) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("scanned", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MakeSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "42"), MkStr(f.arena, "%d"), MakeId(f.arena, "scanned")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), 42u);
}

}  // namespace
